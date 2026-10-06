/* Exercise the real snapshot region manager, including its private cache.
 * Section GC keeps this host-only regression independent of guest execution. */
#include "../../linux-user/snapshot.c"

#include <stdio.h>

/* ASan global registration retains snapshot.c's VM callback table even
 * though section GC normally drops it. This metadata-only unit must never
 * execute a guest-memory callback; fail rather than simulate its result. */
unsigned long guest_base;

static void QEMU_NORETURN unexpected_vm_callback(void)
{
    fputs("snapshot_regions: unexpected guest-VM callback\n", stderr);
    abort();
}

int page_get_flags(target_ulong address)
{
    (void)address;
    unexpected_vm_callback();
}

abi_long target_mmap(abi_ulong start, abi_ulong length, int prot, int flags,
                     int fd, abi_ulong offset)
{
    (void)start; (void)length; (void)prot; (void)flags; (void)fd; (void)offset;
    unexpected_vm_callback();
}

void sem_mem_overwrite(CPUArchState *env, target_ulong address,
                       target_ulong size, SemOpClass cls)
{
    (void)env; (void)address; (void)size; (void)cls;
    unexpected_vm_callback();
}

void sem_reg_overwrite(CPUArchState *env, int reg_idx, SemOpClass cls)
{
    (void)env; (void)reg_idx; (void)cls;
    unexpected_vm_callback();
}

static unsigned checks;
static unsigned failures;

#define CHECK(condition, message) do { \
    checks++; \
    if (!(condition)) { \
        fprintf(stderr, "FAIL snapshot_regions: %s (line %d)\n", \
                message, __LINE__); \
        failures++; \
    } \
} while (0)

static SnapshotMemRegion *lookup_base(target_ulong base)
{
    SnapshotMemRegion query = { .base = base };
    return g_tree_lookup(mr_manager.heap_data, &query);
}

int main(void)
{
    init_mr_manager();
    snapshot_trace_alloc(0x1000, 16, 1);
    snapshot_trace_alloc(0x2000, 32, 2);
    snapshot_trace_alloc(0x3000, 48, 3);
    SnapshotMemRegion *low = mr_manager_heap_search(0x100f);
    SnapshotMemRegion *high = mr_manager_heap_search(0x302f);
    CHECK(low != NULL && low->base == 0x1000, "search reaches smaller key");
    CHECK(high != NULL && high->base == 0x3000, "search reaches larger key");
    CHECK(mr_manager_heap_search(0x1010) == NULL, "heap interval is half-open");

    snapshot_trace_free(0x1001, 4);
    CHECK(lookup_base(0x1000) != NULL, "interior free does not retire allocation");
    snapshot_trace_free(0x1000, 5);
    CHECK(lookup_base(0x1000) == NULL, "free removes non-root exact base");
    CHECK(mr_manager_heap_search(0x1000) == NULL, "free invalidates borrowed cache");

    SnapshotMemRegion *original = mr_manager_heap_search(0x2001);
    CHECK(original != NULL && original->size == 32,
          "original generation is cached before replacement");
    snapshot_trace_alloc(0x2000, 64, 6);
    SnapshotMemRegion *replacement = mr_manager_heap_search(0x2001);
    CHECK(replacement != NULL && replacement->size == 64 && replacement->pc == 6,
          "replacement invalidates the previous cached generation");
    CHECK(mr_manager_heap_search(0x203f) == replacement,
          "duplicate base retains the expanded live extent");
    CHECK(mr_manager_heap_search(0x2040) == NULL, "replacement extent is exact");
    snapshot_trace_free(0x2000, 7);
    CHECK(lookup_base(0x2000) == NULL, "replacement frees exactly once");

    snapshot_trace_alloc(0x4000, 0, 8);
    CHECK(lookup_base(0x4000) != NULL, "zero-size identity is registered");
    snapshot_trace_free(0x4000, 9);
    CHECK(lookup_base(0x4000) == NULL, "zero-size identity can be freed");
    snapshot_trace_alloc(0x4000, 8, 10);
    SnapshotMemRegion *reused = mr_manager_heap_search(0x4007);
    CHECK(reused != NULL && reused->size == 8 && reused->pc == 10,
          "reuse installs a new live extent");

    g_tree_destroy(mr_manager.heap_data);
    g_array_free(mr_manager.stack_data, TRUE);
    g_array_free(mr_manager.global_data, TRUE);
    g_queue_free_full(heap_quarantine, g_free);
    fprintf(stderr, "snapshot_regions: %u/%u checks passed\n",
            checks - failures, checks);
    return failures != 0;
}
