/* Minimal linker environment shared by the focused Stage 3.1 runner. */

#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#include "qemu/osdep.h"
#include "qemu/thread.h"
#include "snapshot.h"
#include "tcg/symbolic/symbolic-struct.h"

unsigned long guest_base = 0;
int binradar_memcheck_enabled = 0;
uint64_t symbolic_start_code = 0;
uint64_t symbolic_end_code = 0;
Expr *pool = NULL;
Expr *next_free_expr = NULL;
Query *query_queue = NULL;
Query *next_query = NULL;

SnapshotMemRegion *mr_manager_heap_search_pub(target_ulong addr)
{
    (void)addr;
    return NULL;
}

void log_msg(const char *fmt, ...)
{
    (void)fmt;
}

bool is_valid_address(target_ulong addr, bool for_snapshot)
{
    (void)addr;
    (void)for_snapshot;
    return false;
}

void qemu_mutex_init(QemuMutex *m)
{
    pthread_mutex_init(&m->lock, NULL);
}

void qemu_mutex_destroy(QemuMutex *m)
{
    pthread_mutex_destroy(&m->lock);
}

void qemu_mutex_lock_impl(QemuMutex *m, const char *file, const int line)
{
    (void)file;
    (void)line;
    pthread_mutex_lock(&m->lock);
}

void qemu_mutex_unlock_impl(QemuMutex *m, const char *file, const int line)
{
    (void)file;
    (void)line;
    pthread_mutex_unlock(&m->lock);
}

QemuMutexLockFunc qemu_mutex_lock_func = qemu_mutex_lock_impl;
QemuMutexTrylockFunc qemu_mutex_trylock_func = NULL;
