/*
 * futex-based synchronization objects
 *
 * Copyright (C) 2018 Zebediah Figura
 * Copyright (C) 2025 Paul Gofman for CodeWeavers
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA
 */

#include "config.h"

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdarg.h>
#include <sys/mman.h>
#include <stdint.h>
#ifdef HAVE_SYS_STAT_H
# include <sys/stat.h>
#endif
#ifdef HAVE_SYS_SYSCALL_H
# include <sys/syscall.h>
#endif
#include <unistd.h>

#include "ntstatus.h"
#define WIN32_NO_STATUS
#include "windef.h"
#include "winternl.h"

#include "handle.h"
#include "request.h"
#include "fsync.h"

#include "pshpack4.h"
#include "poppack.h"

#ifndef __NR_futex_waitv
#define __NR_futex_waitv 449
#endif

int do_fsync_cached = -1;

#ifdef __APPLE__

/* The macOS side of fsync: see dlls/ntdll/unix/fsync.c for how its waits and wakes work here.
 * macOS cannot make a shared memory object bigger once it has a size, so it gets all of it at
 * the start: 1024 pages of objects, each followed by the page that says who sleeps for them,
 * which is room for some four million objects. Pages that are never touched cost nothing. */

#include <AvailabilityMacros.h>
#ifdef MAC_OS_VERSION_14_4
#include <os/os_sync_wait_on_address.h>
#endif

#define FSYNC_MAC_PAGES                     1024
#define FSYNC_CHANNELS                      96
#define FSYNC_UL_COMPARE_AND_WAIT_SHARED    3
#define FSYNC_UL_COMPARE_AND_WAIT64_SHARED  6
#define FSYNC_ULF_WAKE_ALL                  0x00000100

extern int __ulock_wake( uint32_t operation, void *addr, uint64_t wake_value );

static void fsync_shared_wake( void *addr, size_t size )
{
#ifdef MAC_OS_VERSION_14_4
    if (__builtin_available( macOS 14.4, * ))
    {
        os_sync_wake_by_address_all( addr, size, OS_SYNC_WAKE_BY_ADDRESS_SHARED );
        return;
    }
#endif
    __ulock_wake( (size == 8 ? FSYNC_UL_COMPARE_AND_WAIT64_SHARED : FSYNC_UL_COMPARE_AND_WAIT_SHARED) | FSYNC_ULF_WAKE_ALL,
                  addr, 0 );
}

#endif  /* __APPLE__ */
int fsync_check_support(void)
{
#ifdef __linux__
    syscall( __NR_futex_waitv, 0, 0, 0, 0, 0 );
    return getenv( "WINEFSYNC" ) && atoi(getenv( "WINEFSYNC" )) && errno != ENOSYS && errno != EPERM;
#else
#ifdef __APPLE__
    return getenv( "WINEFSYNC" ) && atoi(getenv( "WINEFSYNC" ));
#else
    return 0;
#endif
#endif
}

static char shm_name[29];
static int shm_fd;
static off_t shm_size;
static void **shm_addrs;
static int shm_addrs_size;  /* length of the allocated shm_addrs array */

static int is_fsync_initialized;

static uint64_t *shm_idx_free_map;
static uint32_t shm_idx_free_map_size; /* uint64_t word count */
static uint32_t shm_idx_free_search_start_hint;

#define BITS_IN_FREE_MAP_WORD (8 * sizeof(*shm_idx_free_map))

static void shm_cleanup(void)
{
    close( shm_fd );
    if (shm_unlink( shm_name ) == -1)
        perror( "shm_unlink" );
}

void fsync_init(void)
{
    struct stat st;

    if (fstat( config_dir_fd, &st ) == -1)
        fatal_error( "cannot stat config dir\n" );

    if (st.st_ino != (unsigned long)st.st_ino)
        sprintf( shm_name, "/wine-%lx%08lx-fsync", (unsigned long)((unsigned long long)st.st_ino >> 32), (unsigned long)st.st_ino );
    else
        sprintf( shm_name, "/wine-%lx-fsync", (unsigned long)st.st_ino );

    if (!shm_unlink( shm_name ))
        fprintf( stderr, "fsync: warning: a previous shm file %s was not properly removed\n", shm_name );

    shm_fd = shm_open( shm_name, O_RDWR | O_CREAT | O_EXCL, 0644 );
    if (shm_fd == -1)
        perror( "shm_open" );

    shm_addrs = calloc( 128, sizeof(shm_addrs[0]) );
    shm_addrs_size = 128;

#ifdef __APPLE__
    shm_size = (off_t)FSYNC_MAC_PAGES * 2 * FSYNC_SHM_PAGE_SIZE;
#else
    shm_size = FSYNC_SHM_PAGE_SIZE;
#endif
    if (ftruncate( shm_fd, shm_size ) == -1)
        perror( "ftruncate" );

    is_fsync_initialized = 1;

    fprintf( stderr, "fsync: up and running.\n" );

    shm_idx_free_map_size = 256;
    shm_idx_free_map = malloc( shm_idx_free_map_size * sizeof(*shm_idx_free_map) );
    memset( shm_idx_free_map, 0xff, shm_idx_free_map_size * sizeof(*shm_idx_free_map) );
#ifdef __APPLE__
    /* Nor 1 to 64: the wake channels' counters are where their sleepers would be noted. */
    shm_idx_free_map[0] = 0;
    shm_idx_free_map[1] &= ~(uint64_t)1;
#else
    shm_idx_free_map[0] &= ~(uint64_t)1; /* Avoid allocating shm_index 0. */
#endif

    atexit( shm_cleanup );
}

static struct list mutex_list = LIST_INIT(mutex_list);

struct fsync
{
    struct object  obj;
    unsigned int   shm_idx;
    enum fsync_type type;
    struct list     mutex_entry;
};

static void *get_shm( unsigned int idx )
{
    int entry  = (idx * 16) / FSYNC_SHM_PAGE_SIZE;
    int offset = (idx * 16) % FSYNC_SHM_PAGE_SIZE;

    if (entry >= shm_addrs_size)
    {
        int new_size = max(shm_addrs_size * 2, entry + 1);

        if (!(shm_addrs = realloc( shm_addrs, new_size * sizeof(shm_addrs[0]) )))
            fprintf( stderr, "fsync: couldn't expand shm_addrs array to size %d\n", entry + 1 );

        memset( shm_addrs + shm_addrs_size, 0, (new_size - shm_addrs_size) * sizeof(shm_addrs[0]) );

        shm_addrs_size = new_size;
    }

#ifdef __APPLE__
    if (!shm_addrs[entry])
    {
        /* the page of objects and, right behind it, the page that says who sleeps for them */
        void *addr = mmap( NULL, 2 * FSYNC_SHM_PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED, shm_fd,
                          (off_t)entry * 2 * FSYNC_SHM_PAGE_SIZE );
        if (addr == (void *)-1)
        {
            fprintf( stderr, "fsync: failed to map page %d (offset %#zx): ",
                     entry, (size_t)entry * 2 * FSYNC_SHM_PAGE_SIZE );
            perror( "mmap" );
        }

        if (debug_level)
            fprintf( stderr, "fsync: Mapping page %d at %p.\n", entry, addr );

        if (__sync_val_compare_and_swap( &shm_addrs[entry], 0, addr ))
            munmap( addr, 2 * FSYNC_SHM_PAGE_SIZE ); /* someone beat us to it */
    }
#else
    if (!shm_addrs[entry])
    {
        void *addr = mmap( NULL, FSYNC_SHM_PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED, shm_fd,
                          (off_t)entry * FSYNC_SHM_PAGE_SIZE );
        if (addr == (void *)-1)
        {
            fprintf( stderr, "fsync: failed to map page %d (offset %#zx): ",
                     entry, (size_t)entry * FSYNC_SHM_PAGE_SIZE );
            perror( "mmap" );
        }

        if (debug_level)
            fprintf( stderr, "fsync: Mapping page %d at %p.\n", entry, addr );

        if (__sync_val_compare_and_swap( &shm_addrs[entry], 0, addr ))
            munmap( addr, FSYNC_SHM_PAGE_SIZE ); /* someone beat us to it */
    }
#endif

    return (void *)((unsigned long)shm_addrs[entry] + offset);
}

static int alloc_shm_idx_from_word( unsigned int word_index )
{
    int ret;

    if (!shm_idx_free_map[word_index]) return 0;

    ret = __builtin_ctzll( shm_idx_free_map[word_index] );
    shm_idx_free_map[word_index] &= ~((uint64_t)1 << ret);
    shm_idx_free_search_start_hint = shm_idx_free_map[word_index] ? word_index : word_index + 1;
    return word_index * BITS_IN_FREE_MAP_WORD + ret;
}

unsigned int fsync_alloc_shm( int low, int high )
{
#ifdef __linux__
    unsigned int i;
    int shm_idx;
    int *shm;

    /* this is arguably a bit of a hack, but we need some way to prevent
     * allocating shm for the master socket */
    if (!is_fsync_initialized)
        return 0;

    /* shm_idx_free_search_start_hint is always at the first word with a free index or before that. */
    for (i = shm_idx_free_search_start_hint; i < shm_idx_free_map_size; ++i)
        if ((shm_idx = alloc_shm_idx_from_word( i ))) break;

    if (!shm_idx)
    {
        uint32_t old_size, new_size;
        uint64_t *new_alloc;

        old_size = shm_idx_free_map_size;
        new_size = old_size + 256;
        new_alloc = realloc( shm_idx_free_map, new_size * sizeof(*new_alloc) );
        if (!new_alloc)
        {
            fprintf( stderr, "fsync: couldn't expand shm_idx_free_map to size %zd.",
                new_size * sizeof(*new_alloc) );
            return 0;
        }
        memset( new_alloc + old_size, 0xff, (new_size - old_size) * sizeof(*new_alloc) );
        shm_idx_free_map = new_alloc;
        shm_idx_free_map_size = new_size;
        shm_idx = alloc_shm_idx_from_word( old_size );
    }

    while (shm_idx * 16 >= shm_size)
    {
        /* Better expand the shm section. */
        shm_size += FSYNC_SHM_PAGE_SIZE;
        if (ftruncate( shm_fd, shm_size ) == -1)
        {
            fprintf( stderr, "fsync: couldn't expand %s to size %jd: ",
                shm_name, shm_size );
            perror( "ftruncate" );
        }
    }

    shm = get_shm( shm_idx );
    assert(shm);
    shm[0] = low;
    shm[1] = high;
    shm[2] = 1; /* Reference count. */
    shm[3] = 0; /* Last reference process id. */

    return shm_idx;
#else
#ifdef __APPLE__
    static int warned;
    unsigned int i;
    int shm_idx;
    int *shm;

    /* as on Linux, nothing for the master socket */
    if (!is_fsync_initialized)
        return 0;

    for (i = shm_idx_free_search_start_hint; i < shm_idx_free_map_size; ++i)
        if ((shm_idx = alloc_shm_idx_from_word( i ))) break;

    if (!shm_idx)
    {
        uint32_t old_size, new_size;
        uint64_t *new_alloc;

        old_size = shm_idx_free_map_size;
        new_size = old_size + 256;
        /* the shared memory has its size for good here: no index past its end */
        if ((uint64_t)new_size * BITS_IN_FREE_MAP_WORD * 16 > (uint64_t)FSYNC_MAC_PAGES * FSYNC_SHM_PAGE_SIZE
            || !(new_alloc = realloc( shm_idx_free_map, new_size * sizeof(*new_alloc) )))
        {
            if (!warned++) fprintf( stderr, "fsync: no room for more objects in the shared memory.\n" );
            return 0;
        }
        memset( new_alloc + old_size, 0xff, (new_size - old_size) * sizeof(*new_alloc) );
        shm_idx_free_map = new_alloc;
        shm_idx_free_map_size = new_size;
        shm_idx = alloc_shm_idx_from_word( old_size );
    }

    shm = get_shm( shm_idx );
    assert(shm);
    shm[0] = low;
    shm[1] = high;
    shm[2] = 1; /* Reference count. */
    shm[3] = 0; /* Last reference process id. */
    memset( (char *)shm + FSYNC_SHM_PAGE_SIZE, 0, 16 ); /* nobody sleeps for it */

    return shm_idx;
#else
    return 0;
#endif
#endif
}

void fsync_free_shm_idx( int shm_idx )
{
    unsigned int idx;
    uint64_t mask;
    int *shm;

    if (!shm_idx) return;
    assert( shm_idx > 0 && shm_idx < shm_idx_free_map_size * BITS_IN_FREE_MAP_WORD );

    shm = get_shm( shm_idx );
    if (shm[2] <= 0)
    {
        fprintf( stderr, "wineserver: fsync err: shm refcount is %d.\n", shm[2] );
        return;
    }

    if (__atomic_sub_fetch( &shm[2], 1, __ATOMIC_SEQ_CST ))
    {
        /* Sync object is still referenced in a process. */
        return;
    }

    idx = shm_idx / BITS_IN_FREE_MAP_WORD;
    mask = (uint64_t)1 << (shm_idx % BITS_IN_FREE_MAP_WORD);
    assert( !(shm_idx_free_map[idx] & mask) );
    shm_idx_free_map[idx] |= mask;
    if (idx < shm_idx_free_search_start_hint)
        shm_idx_free_search_start_hint = idx;
}

/* Try to cleanup the shared mem indices locked by the wait on the killed processes.
 * This is not fully reliable but should avoid leaking the majority of indices on
 * process kill. */
void fsync_cleanup_process_shm_indices( process_id_t id )
{
    uint64_t free_word;
    unsigned int i, j;
    void *shmbase;
    int *shm;

    for (i = 0; i < shm_idx_free_map_size; ++i)
    {
        free_word = shm_idx_free_map[i];
        if (free_word == ~(uint64_t)0) continue;
        shmbase = get_shm( i * BITS_IN_FREE_MAP_WORD );
        for (j = !i; j < BITS_IN_FREE_MAP_WORD; ++j)
        {
            shm = (int *)((char *)shmbase + j * 16);
            if (!(free_word & ((uint64_t)1 << j)) && shm[3] == id
                  && __atomic_load_n( &shm[2], __ATOMIC_SEQ_CST ) == 1)
                fsync_free_shm_idx( i * BITS_IN_FREE_MAP_WORD + j );
        }
    }
}

int fsync_grab_shm_idx( unsigned int shm_idx )
{
    int *shm;

    shm = get_shm( shm_idx );
    __atomic_add_fetch( &shm[2], 1, __ATOMIC_SEQ_CST );
    return shm_idx;
}

#ifdef __APPLE__

/* wake everything that sleeps for an object whose state was just changed: as futex_wake() in
 * dlls/ntdll/unix/fsync.c */
static inline int futex_wake( int *addr, int val )
{
    unsigned int *sleepers = (unsigned int *)(((unsigned long)addr & ~15ul) + FSYNC_SHM_PAGE_SIZE), bits, i;
    uint64_t *channels = (uint64_t *)((char *)get_shm( 1 ) + FSYNC_SHM_PAGE_SIZE);

    __sync_synchronize();
    if (__atomic_load_n( &sleepers[3], __ATOMIC_SEQ_CST )) fsync_shared_wake( addr, 4 );
    for (i = 0; i < FSYNC_CHANNELS / 32; i++)
    {
        if (!__atomic_load_n( &sleepers[i], __ATOMIC_SEQ_CST )) continue;
        bits = __atomic_exchange_n( &sleepers[i], 0, __ATOMIC_SEQ_CST );
        while (bits)
        {
            uint64_t *channel = channels + i * 32 + __builtin_ctz( bits );

            bits &= bits - 1;
            __atomic_add_fetch( channel, 1, __ATOMIC_SEQ_CST );
            fsync_shared_wake( channel, 8 );
        }
    }
    return 0;
}

#else
static inline int futex_wake( int *addr, int val )
{
#ifdef __NR_futex
    return syscall( __NR_futex, addr, 1, val, NULL, 0, 0 );
#else
    errno = ENOSYS;
    return -1;
#endif
}
#endif

/* shm layout for events or event-like objects. */
struct fsync_event
{
    int signaled;
    int unused;
    int ref;
    int last_pid;
};

void fsync_set_event( unsigned int shm_idx )
{
    struct fsync_event *event = get_shm( shm_idx );

    if (!__atomic_exchange_n( &event->signaled, 1, __ATOMIC_SEQ_CST ))
        futex_wake( &event->signaled, INT_MAX );
}

void fsync_reset_event( unsigned int shm_idx )
{
    struct fsync_event *event = get_shm( shm_idx );

    __atomic_store_n( &event->signaled, 0, __ATOMIC_SEQ_CST );
}

struct mutex
{
    int tid;
    int count;  /* recursion count */
};

void fsync_abandon_mutex( unsigned int shm_idx, thread_id_t tid )
{
    struct mutex *mutex = get_shm( shm_idx );

    if (mutex->tid != tid) return;

    if (debug_level)
        fprintf( stderr, "fsync_abandon_mutexes() idx=%d\n", shm_idx );

    mutex->tid = ~0;
    mutex->count = 0;
    futex_wake( &mutex->tid, INT_MAX );
}

DECL_HANDLER(fsync_free_shm_idx)
{
    if (!req->shm_idx || req->shm_idx >= shm_idx_free_map_size * BITS_IN_FREE_MAP_WORD)
    {
        set_error( STATUS_INVALID_PARAMETER );
        return;
    }
    fsync_free_shm_idx( req->shm_idx );
}
