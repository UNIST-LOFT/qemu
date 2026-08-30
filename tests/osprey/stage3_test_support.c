/* Minimal linker environment shared by the focused OSPREY unit runners. */

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

void osprey_test_log_reset(void);
const char *osprey_test_log_contents(void);

SnapshotMemRegion *mr_manager_heap_search_pub(target_ulong addr)
{
    (void)addr;
    return NULL;
}

#define TEST_LOG_CAPACITY (UINT64_C(1) << 20)

static char test_log_buffer[TEST_LOG_CAPACITY];
static size_t test_log_length;

void osprey_test_log_reset(void)
{
    test_log_length = 0;
    test_log_buffer[0] = '\0';
}

const char *osprey_test_log_contents(void)
{
    return test_log_buffer;
}

void log_msg(const char *fmt, ...)
{
    va_list args;
    int written;
    size_t remaining;

    if (fmt == NULL || test_log_length >= sizeof(test_log_buffer) - 1u) return;
    remaining = sizeof(test_log_buffer) - test_log_length;
    va_start(args, fmt);
    written = vsnprintf(&test_log_buffer[test_log_length], remaining,
                        fmt, args);
    va_end(args);
    if (written < 0) return;
    if ((size_t)written >= remaining) {
        test_log_length = sizeof(test_log_buffer) - 1u;
    } else {
        test_log_length += (size_t)written;
    }
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
