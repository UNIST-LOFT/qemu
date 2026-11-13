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

static void test_stack_lookup(void)
{
    snapshot_trace_stack_call(0x1000000, 0x10, 0x20);
    SnapshotMemRegion *outer = mr_manager_stack_search(0xfff000, 8);
    CHECK(outer != NULL && outer->size == 0x1000,
          "access below observed stack grows the top frame");
    snapshot_trace_stack_call(0xfff800, 0x30, 0x40);
    SnapshotMemRegion *inner = mr_manager_stack_search(0xfff7f8, 8);
    CHECK(inner != NULL && inner != outer,
          "newest containing frame wins overlapping lookup");
    CHECK(mr_manager_stack_search(0xfff7ff, 2) == outer,
          "whole access crossing inner end resolves to outer frame");
    CHECK(mr_manager_stack_search(0xfff700, 8) == outer && inner->size == 8,
          "existing outer coverage wins before lazy inner growth");
    snapshot_trace_alloc(0xfff000, 0x1000, 0x50);
    CHECK(snapshot_mem_region_search_with_size(0xfff7f8, 8) == inner,
          "stack priority survives overlapping heap coverage");
    snapshot_trace_free(0xfff000, 0x60);

    target_ulong low = 0xfff7f8 - SNAPSHOT_STACK_LAZY_WINDOW;
    CHECK(mr_manager_stack_search(low, 8) == inner &&
              inner->size == 8 + SNAPSHOT_STACK_LAZY_WINDOW,
          "envelope miss retains inclusive lazy-growth boundary");
    CHECK(mr_manager_stack_search(low - SNAPSHOT_STACK_LAZY_WINDOW - 1, 1)
              == NULL,
          "access beyond lazy window remains unclassified");
    CHECK(mr_manager_stack_search(0xfff7f8, 0) == NULL,
          "zero-width stack access is rejected");
    CHECK(mr_manager_stack_search((target_ulong)-4, 8) == NULL,
          "wrapping stack interval is rejected");
    CHECK(mr_manager_stack_search(0x1000000, 1) == NULL,
          "stack upper endpoint remains excluded");
    snapshot_trace_stack_ret(0xfff800, 0x40);
    CHECK(mr_manager.stack_region.base == 0x1000000 &&
              mr_manager.stack_region.size == 0x1000,
          "pop removes the departed frame's envelope extension");
    CHECK(mr_manager_stack_search(0xfff7f8, 8) == outer,
          "pop restores the surviving frame identity");
    snapshot_trace_stack_ret(0x1000000, 0x20);
    CHECK(mr_manager_stack_search(0xfff7f8, 8) == NULL,
          "empty stack retains no stale region");

    snapshot_trace_stack_call(4, 0x70, 0x80);
    CHECK(mr_manager_stack_search(0, 4) != NULL &&
              mr_manager_stack_search(0, 5) == NULL,
          "near-zero frame bounds do not wrap");
    snapshot_trace_stack_ret(4, 0x80);

    /* Non-top overlap: the newest frame does not contain the access, so an
     * older frame must still be found even though the envelope check alone
     * would have allowed a full scan. */
    snapshot_trace_stack_call(0x3000000, 0xc0, 0xd0);
    snapshot_trace_stack_call(0x2fff000, 0xe0, 0xf0);
    snapshot_trace_stack_call(0x2ffe000, 0x100, 0x110);
    CHECK(mr_manager_stack_search(0x2fff800, 8) != NULL,
          "overlap resolves inside a non-top frame");
    snapshot_trace_stack_ret(0x2ffe000, 0x110);
    snapshot_trace_stack_ret(0x2fff000, 0xf0);
    snapshot_trace_stack_ret(0x3000000, 0xd0);
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

    test_stack_lookup();

    g_tree_destroy(mr_manager.heap_data);
    g_array_free(mr_manager.stack_data, TRUE);
    g_array_free(mr_manager.global_data, TRUE);
    g_queue_free_full(heap_quarantine, g_free);
    fprintf(stderr, "snapshot_regions: %u/%u checks passed\n",
            checks - failures, checks);
    return failures != 0;
}
