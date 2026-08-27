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

typedef struct Expr Expr;
typedef struct Query Query;

void trace_mem(const char* fmt, ...);
void log_msg(const char *fmt, ...);

extern bool restoring_to_snapshot;
extern target_ulong binradar_entrypoint;
extern unsigned char afl_fork_child;

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
    bool         valid;
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

typedef struct {
    uint64_t from;
    uint64_t to;
} CoverageEdge;

typedef struct ArgumentInfo {
    uint8_t reg;
    const char *reg_name;
    target_ulong value;
    Expr *expr;
} ArgumentInfo;

void add_exclude_regions(uintptr_t load_bias);
bool is_in_exclude_region(target_ulong pc);
void parse_e9_relocated_calls(uintptr_t load_bias);
void check_all_env_var(void);

void snapshot_set_binradar_patch_shm(uint32_t *shm);
const char *snapshot_mem_region_str(SnapshotMemRegion *mr);

guint coverage_edge_hash(gconstpointer key);
gboolean coverage_edge_equal(gconstpointer a, gconstpointer b);
CoverageEdge* coverage_edge_copy(const CoverageEdge* edge);

bool is_valid_address(target_ulong addr, bool for_snapshot);

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
void snapshot_bind_read_expr(uintptr_t addr, uintptr_t size, Expr *expr);

void snapshot_trace_pending_allocs(target_ulong size, target_ulong pc);
PendingAlloc snapshot_trace_get_pending_allocs(target_ulong pc);
void snapshot_trace_alloc(target_ulong base, target_ulong size, target_ulong pc);
void snapshot_trace_free(target_ulong base, target_ulong pc);
void snapshot_trace_stack_call(target_ulong sp, target_ulong call_pc, target_ulong ret_pc);
void snapshot_trace_stack_ret(target_ulong sp, target_ulong actual_ret_pc);
void snapshot_trace_stack_push(target_ulong sp, target_ulong pc);
void snapshot_trace_stack_pop(target_ulong sp);
void snapshot_trace_global_add(target_ulong base, target_ulong size, target_ulong pc, const char *name);
SnapshotMemRegion *snapshot_mem_region_search_with_size(target_ulong addr, target_ulong size);
SnapshotMemRegion *snapshot_mem_region_search(target_ulong addr);
void snapshot_protect_mapping(target_ulong addr, target_ulong len);
bool snapshot_addr_is_protected(target_ulong addr);

/* ---- QASAN-like concrete bounds checking ---- */
extern int binradar_memcheck_enabled;

typedef enum {
    MEMCHECK_OK = 0,
    MEMCHECK_HEAP_OOB,
    MEMCHECK_HEAP_UAF,
} MemcheckResult;

MemcheckResult snapshot_memcheck_access(target_ulong addr, target_ulong size);
void snapshot_memcheck_helper(target_ulong addr, target_ulong size, target_ulong pc);

void snapshot_syscall(uintptr_t syscall_no, uintptr_t syscall_arg0,
                      uintptr_t syscall_arg1, uintptr_t syscall_arg2,
                      uintptr_t syscall_arg3, uintptr_t syscall_arg4,
                      uintptr_t syscall_arg5, uintptr_t syscall_arg6,
                      uintptr_t ret_val);
void snapshot_syscall_munmap(target_ulong addr, target_ulong len);
int snapshot_is_unmap_allowed(target_ulong addr, target_ulong len);

void snapshot_add_mapping(target_ulong addr, target_ulong len);
SnapshotMemRegion *mr_manager_heap_search_pub(target_ulong addr);
void snapshot_remove_mapping(target_ulong addr, target_ulong len);

void snapshot_fork_setup(void);
void snapshot_forkserver(CPUState *cpu, CPUArchState *cpu_env, const ArgumentInfo *arg_info, size_t num_arg_regs);
void snapshot_maybe_forkserver(CPUState *cpu, CPUArchState *cpu_env, target_ulong pc);

uint8_t snapshot_on_entrypoint_hit(target_ulong pc);

void snapshot_load_inferred_types(uint8_t *analyze_result);

#endif /* BINRADAR_SNAPSHOT_H */
