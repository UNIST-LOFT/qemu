#ifndef BINRADAR_SNAPSHOT_H
#define BINRADAR_SNAPSHOT_H

#include "qemu/osdep.h"
#include "qemu.h"

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdarg.h>

void trace_mem(const char* fmt, ...);

extern bool restoring_to_snapshot;
extern target_ulong binradar_entrypoint;

#define SNAPSHOT_PAGE_SIZE 4096
#define SNAPSHOT_PAGE_MASK ~(SNAPSHOT_PAGE_SIZE - 1)

#define MAX_POINTER_ACCESS 4096
#define MAX_PRIMITIVE_ACCESS 4096

typedef struct {
    target_ulong addr;
    int perms;
    void *data;
} SnapshotPageInfo;

typedef struct {
    target_ulong access_cache[4];
    int access_cache_idx;
    GHashTable *dirty_pages;
} SnapshotTLS;

typedef struct {
    target_ulong start;
    target_ulong len;
} SnapshotMapping;

typedef struct {
    GHashTable *pages;
    target_ulong start_brk;
    target_ulong start_mmap;
    
    GList *new_mappings;
    
    CPUArchState *cpu_state;
    
    bool is_snapshot_taken;
} SnapshotState;

typedef struct {
    bool         is_heap;
    bool         is_stack; // else: global
    // For stack: base is the top of the stack frame
    // For heap/global: base is the lowest address
    target_ulong base;
    target_ulong size;
    target_ulong pc;
} SnapshotMemRegion;

typedef struct {
    target_ulong size;
    target_ulong pc;
} PendingAlloc;

typedef struct {
    bool symbolic_addr;
    bool symbolic_value;
    uintptr_t addr;
    uintptr_t pc;
    uint8_t target[8];
    uint8_t *ptr;
    uintptr_t size;
} SnapshotMemAccess;

typedef struct {
    uintptr_t base;
    uint64_t offset;
} PointerDecomposition;

typedef struct {
    int shared_index;
    uintptr_t key;
    void *data;
    GList *node;
} OrderedMapEntry;

// Ordered map
// Key: uintptr_t
typedef struct {
    GHashTable *table;
    GQueue *queue;
    int max_size;
} OrderedMap;

bool is_valid_address(target_ulong addr);

OrderedMap *ordered_map_init(int max_size);
OrderedMapEntry *ordered_map_insert(OrderedMap *map, uintptr_t key, void *data);
OrderedMapEntry* ordered_map_lookup(OrderedMap *map, uintptr_t key);

void snapshot_record_guest_normal_exit(CPUArchState *cpu_env, int exit_code, const char *reason);
void snapshot_record_guest_crash(CPUArchState *cpu_env, int target_signal,
                                 int host_signal, int si_code,
                                 target_ulong fault_addr,
                                 uintptr_t host_fault_addr,
                                 const char *reason);

void snapshot_init(void);
bool snapshot_is_taken(void);
void snapshot_save(void);
// void snapshot_restore(CPUArchState *cpu);

void snapshot_write_access(SnapshotMemAccess *mem_access);
void snapshot_read_access(SnapshotMemAccess *mem_access);

void snapshot_trace_pending_allocs(target_ulong size, target_ulong pc);
PendingAlloc snapshot_trace_get_pending_allocs(target_ulong pc);
void snapshot_trace_alloc(target_ulong base, target_ulong size, target_ulong pc);
void snapshot_trace_free(target_ulong base, target_ulong pc);
void snapshot_trace_stack_push(target_ulong sp, target_ulong pc);
void snapshot_trace_stack_pop(target_ulong sp);
void snapshot_trace_global_add(target_ulong base, target_ulong size, target_ulong pc, const char *name);
SnapshotMemRegion *snapshot_mem_region_search(target_ulong addr);

void snapshot_syscall(uintptr_t syscall_no, uintptr_t syscall_arg0,
                      uintptr_t syscall_arg1, uintptr_t syscall_arg2,
                      uintptr_t syscall_arg3, uintptr_t syscall_arg4,
                      uintptr_t syscall_arg5, uintptr_t syscall_arg6,
                      uintptr_t ret_val);
void snapshot_syscall_munmap(target_ulong addr, target_ulong len);
int snapshot_is_unmap_allowed(target_ulong addr, target_ulong len);

void snapshot_add_mapping(target_ulong addr, target_ulong len);
void snapshot_remove_mapping(target_ulong addr, target_ulong len);

void snapshot_fork_setup(void);
void snapshot_forkserver(CPUState *cpu);

#endif /* BINRADAR_SNAPSHOT_H */
