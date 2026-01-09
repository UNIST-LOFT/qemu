#include "snapshot.h"
#include "../tcg/symbolic/symbolic-struct.h"

#include "qemu/rcu.h"

#include <stdio.h>
#include <stdint.h>

#define SNAPSHOT_EXIT_DESC_LEN 256
#define SNAPSHOT_BT_DEPTH 64
// #define SNAPSHOT_DEBUG

#ifdef SNAPSHOT_DEBUG
#include <execinfo.h>
#include <signal.h>
#include <unistd.h>
#endif

#include <sys/mman.h>

#define FORKSRV_FD 198

extern target_ulong target_brk;
bool restoring_to_snapshot;
target_ulong binradar_entrypoint = (target_ulong)-1;

bool forkserver_installed = false;
unsigned char afl_fork_child;
unsigned int  afl_forksrv_pid;

static SnapshotState g_snapshot;

#define SNAPSHOT_MEM_REG_CACHE 4
#define SNAPSHOT_STACK_LAZY_WINDOW (SNAPSHOT_PAGE_SIZE * 16)
typedef struct {
    // Determine region by address
    SnapshotMemRegion stack_region;
    SnapshotMemRegion global_region; // else: heap
    // Cache
    // Don't use stack cache for now
    // int stack_cache_index;
    int heap_cache_index;
    int global_cache_index;
    // SnapshotMemRegion* stack_cache[SNAPSHOT_MEM_REG_CACHE];
    SnapshotMemRegion* heap_cache[SNAPSHOT_MEM_REG_CACHE];
    SnapshotMemRegion* global_cache[SNAPSHOT_MEM_REG_CACHE];
    // Data
    GArray *stack_data;
    GTree *heap_data;
    GArray *global_data;
} SnapshotMemRegionManager;

static SnapshotMemRegionManager mr_manager;
static GArray *pending_allocs = NULL;

// TODO: add trace or coverage info
typedef struct {
    uint32_t valid;
    uint32_t crashed;
    int32_t target_signal;
    int32_t host_signal;
    int32_t si_code;
    int32_t exit_code;
    target_ulong guest_pc;
    target_ulong guest_cs_base;
    target_ulong fault_addr;
    uintptr_t host_fault_addr;
    uint64_t guest_last_translation_block;
    Expr *next_free_expr;
    Query *next_query;
    // uint32_t bt_depth;
    // uintptr_t bt[SNAPSHOT_BT_DEPTH];
    char description[SNAPSHOT_EXIT_DESC_LEN];
} SnapshotExitInfo;

typedef struct {
    uintptr_t addr;
    uintptr_t size;
    uint8_t target[8];
} SingleModification;

typedef struct {
    GQueue *modifications; // Queue<Array<SingleModification>>
    GArray *current; // Array<SingleModification>
    GArray *done;    // Array<Array<SingleModification>>
} ModificationManager;

typedef struct {
    int size;
    uintptr_t addr;
    uintptr_t pc;
    uint64_t access_id;
} PrimitiveAccess;

typedef struct {
    uintptr_t addr;
    uintptr_t target;
    uintptr_t pc;
    uint64_t access_id;
} PointerAccess;

typedef struct {
    uint32_t prim_idx;
    uint32_t ptr_idx;
    uint64_t prim_access_cnt;
    uint64_t ptr_access_cnt;
    SnapshotExitInfo exit_info;
    PrimitiveAccess primitives[MAX_PRIMITIVE_ACCESS];
    PointerAccess pointers[MAX_POINTER_ACCESS];
} SharedTraceData;

static SharedTraceData *shared_trace_data = NULL;

static OrderedMap *g_read_access_tainted_primitives = NULL;
static OrderedMap *g_read_access_pointers = NULL;

static GHashTable *g_read_access_tainted_primitives_original = NULL;
static GHashTable *g_read_access_pointers_original = NULL;

static GHashTable *g_read_access_tainted_primitives_all = NULL;
static GHashTable *g_read_access_pointers_all = NULL;

static ModificationManager *mod_manager = NULL;
static SnapshotExitInfo original_exit_info;

static int   use_trace = -1;
static FILE* trace_file_fp;

void trace_mem(const char* fmt, ...) {
    if (use_trace == -1 && trace_file_fp == NULL) {
        char* trace_file = getenv("BINRADAR_TRACE_FILE");
        if (trace_file == NULL) {
            use_trace = 1;
        } else if (strcmp(trace_file, "none") == 0) {
            use_trace = 0;
        } else {
            use_trace = 1;
            trace_file_fp = fopen(trace_file, "a");
            if (trace_file_fp == NULL) {
                fprintf( stderr, "ERROR: cannot open trace file %s\n",
                        trace_file);
                exit(1);
            }
        }
    }
    if (!use_trace)
        return;
    va_list ap;
    va_start(ap, fmt);
    if (trace_file_fp) {
        vfprintf(trace_file_fp, fmt, ap);
    } else {
        vfprintf( stderr, fmt, ap);
    }
    va_end(ap);
}

OrderedMap *ordered_map_init(int max_size) {
    OrderedMap *map = g_new(OrderedMap, 1);
    map->max_size = max_size;
    map->table = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, g_free);
    map->queue = g_queue_new();
    return map;
}

OrderedMapEntry *ordered_map_insert(OrderedMap *map, uintptr_t key, void *data) {
    OrderedMapEntry *existing = g_hash_table_lookup(map->table, GUINT_TO_POINTER(key));
    int old_index = -1;
    if (existing != NULL) {
        old_index = existing->shared_index;
        g_queue_delete_link(map->queue, existing->node);
        g_hash_table_remove(map->table, GUINT_TO_POINTER(key));
    }

    if (map->max_size > 0 && g_queue_get_length(map->queue) >= map->max_size) {
        OrderedMapEntry *oldest_entry = (OrderedMapEntry *)g_queue_pop_head(map->queue);
        if (oldest_entry != NULL) {
            old_index = oldest_entry->shared_index;
            uintptr_t old_key = oldest_entry->key;
            g_hash_table_remove(map->table, GUINT_TO_POINTER(old_key));
        }
    }

    OrderedMapEntry *entry = g_new(OrderedMapEntry, 1);
    memset(entry, 0, sizeof(OrderedMapEntry));
    entry->key = key;
    entry->data = data;
    entry->shared_index = old_index;

    g_queue_push_tail(map->queue, entry);
    entry->node = map->queue->tail;
    g_hash_table_insert(map->table, GUINT_TO_POINTER(key), entry);
    return entry;
}

OrderedMapEntry* ordered_map_lookup(OrderedMap *map, uintptr_t key) {
    OrderedMapEntry *entry = (OrderedMapEntry *)g_hash_table_lookup(map->table, GUINT_TO_POINTER(key));
    return entry;
}

static SnapshotExitInfo *snapshot_exit_info_ptr(void) {
    if (shared_trace_data == NULL) return NULL;
    return &shared_trace_data->exit_info;
}

static void snapshot_exit_info_capture(SnapshotExitInfo *info, CPUArchState *env) {
    if (!info || !env) return;
    target_ulong pc = 0;
    target_ulong cs_base = 0;
    uint32_t flags = 0;
    cpu_get_tb_cpu_state(env, &pc, &cs_base, &flags);
    info->guest_pc = pc;
    info->guest_cs_base = cs_base;
    info->guest_last_translation_block = last_translation_block;
    info->next_free_expr = next_free_expr;
    info->next_query = next_query;
}

static void snapshot_exit_info_set_reason(SnapshotExitInfo *info, const char *reason) {
    if (!info) return;
    if (!reason) {
        info->description[0] = '\0';
        return;
    }
    g_strlcpy(info->description, reason, SNAPSHOT_EXIT_DESC_LEN);
}

static bool snapshot_exit_info_should_update(const SnapshotExitInfo *info, bool crashed) {
    if (info == NULL) return false;
    if (!info->valid) return true;
    return crashed;  // Prevent update for exit() after error handling
}

void snapshot_record_guest_normal_exit(CPUArchState *cpu_env, int exit_code, const char *reason) {
    SnapshotExitInfo *info = snapshot_exit_info_ptr();
    if (!snapshot_exit_info_should_update(info, false)) return;
    info->valid = 1;
    info->crashed = 0;
    info->exit_code = exit_code;
    snapshot_exit_info_capture(info, cpu_env);
    snapshot_exit_info_set_reason(info, reason ? reason : "normal_exit");
}

void snapshot_record_guest_crash(CPUArchState *cpu_env, int target_signal, int host_signal, int si_code, target_ulong fault_addr, uintptr_t host_fault_addr, const char *reason) {
    SnapshotExitInfo *info = snapshot_exit_info_ptr();
    if (!snapshot_exit_info_should_update(info, true)) return;
    info->valid = 1;
    info->crashed = 1;
    info->target_signal = target_signal;
    info->host_signal = host_signal;
    info->si_code = si_code;
    info->exit_code = (host_signal > 0) ? (128 + host_signal) : -target_signal;
    info->fault_addr = fault_addr;
    info->host_fault_addr = host_fault_addr;
    snapshot_exit_info_capture(info, cpu_env);
    char buffer[SNAPSHOT_EXIT_DESC_LEN];
    const char *base = reason ? reason : "unhandled signal";
    const char *host_name = (host_signal > 0) ? strsignal(host_signal) : NULL;
    if (host_name) {
        g_snprintf(buffer, sizeof(buffer), "%s (host=%s[%d], target=%d)", base, host_name, host_signal, target_signal);
    } else {
        g_snprintf(buffer, sizeof(buffer), "%s (host=%d, target=%d)", base, host_signal, target_signal);
    }
    snapshot_exit_info_set_reason(info, buffer);
}

static void remove_read_access_primitive(uintptr_t addr) {
    if (g_read_access_tainted_primitives == NULL) return;
    OrderedMapEntry *entry = ordered_map_lookup(g_read_access_tainted_primitives, addr);
    if (entry == NULL) return;
    // Remove from queue
    int idx_to_remove = entry->shared_index;
    g_queue_delete_link(g_read_access_tainted_primitives->queue, entry->node);
    int last_idx = __atomic_sub_fetch(&shared_trace_data->prim_idx, 1, __ATOMIC_RELAXED);
    if (idx_to_remove < last_idx) {
        PrimitiveAccess *src = &shared_trace_data->primitives[last_idx];
        PrimitiveAccess *dst = &shared_trace_data->primitives[idx_to_remove];
        *dst = *src;
        OrderedMapEntry *moved_entry = ordered_map_lookup(g_read_access_tainted_primitives, dst->addr);
        if (moved_entry != NULL) {
            moved_entry->shared_index = idx_to_remove;
            moved_entry->data = dst;
        }
        memset(src, 0, sizeof(PrimitiveAccess));
    } else if (idx_to_remove == last_idx) {
        memset(&shared_trace_data->primitives[idx_to_remove], 0, sizeof(PrimitiveAccess));
    } else {
        trace_mem("[rpi] ERROR! remove primtive failed! idx %d > last %d\n", idx_to_remove, last_idx);
    }
    g_hash_table_remove(g_read_access_tainted_primitives->table, GUINT_TO_POINTER(addr));
}

static void add_read_access_pointer(uintptr_t addr, uintptr_t target, uintptr_t pc) {
    if (shared_trace_data == NULL) return;
    if (g_read_access_pointers == NULL) g_read_access_pointers = ordered_map_init(MAX_POINTER_ACCESS);
    OrderedMapEntry *entry = ordered_map_insert(g_read_access_pointers, addr, NULL);
    PointerAccess *ptr = NULL;
    if (entry->shared_index < 0) {
        int new_index = __atomic_fetch_add(&shared_trace_data->ptr_idx, 1, __ATOMIC_RELAXED);
        entry->shared_index = new_index;
        if (new_index < MAX_POINTER_ACCESS) {
            ptr = &shared_trace_data->pointers[new_index];
        }
    } else if (entry->shared_index < MAX_POINTER_ACCESS) {
        ptr = &shared_trace_data->pointers[entry->shared_index];
    }
    if (ptr == NULL) {
        trace_mem("[rpo] ptr shared_index error!!! %d\n", entry->shared_index);
        exit(1);
    }
    ptr->addr = addr;
    ptr->target = target;
    ptr->pc = pc;
    ptr->access_id = __atomic_fetch_add(&shared_trace_data->ptr_access_cnt, 1, __ATOMIC_RELAXED);
    entry->data = ptr;
    trace_mem("[rpo] [addr %lx] [target %lx] [pc %lx] [index %d] [id %ld]\n", addr, target, pc, entry->shared_index, ptr->access_id);
}

static void add_read_access_primitive(uintptr_t addr, int size, uintptr_t pc) {
    if (shared_trace_data == NULL) return;
    if (g_read_access_pointers) {
        uintptr_t aligned_addr = addr & ~(uintptr_t)0x07;
        OrderedMapEntry *ptr_entry = ordered_map_lookup(g_read_access_pointers, aligned_addr);
        if (ptr_entry != NULL) {
            remove_read_access_primitive(addr);
            return;
        }
    }
    if (g_read_access_tainted_primitives == NULL) g_read_access_tainted_primitives = ordered_map_init(MAX_PRIMITIVE_ACCESS);
    PrimitiveAccess *prim = NULL;
    OrderedMapEntry *entry = ordered_map_insert(g_read_access_tainted_primitives, addr, NULL);
    if (entry->shared_index < 0) {
        int new_index = __atomic_fetch_add(&shared_trace_data->prim_idx, 1, __ATOMIC_RELAXED);
        entry->shared_index = new_index;
        if (new_index < MAX_PRIMITIVE_ACCESS) {
            prim = &shared_trace_data->primitives[new_index];
        }
    } else if (entry->shared_index < MAX_PRIMITIVE_ACCESS) {
        prim = &shared_trace_data->primitives[entry->shared_index];
    }
    if (prim == NULL) {
        trace_mem("[rpo] prim shared_index error!!! %d\n", entry->shared_index);
        exit(1);
    }
    prim->addr = addr;
    prim->size = size;
    prim->pc = pc;
    prim->access_id = __atomic_fetch_add(&shared_trace_data->prim_access_cnt, 1, __ATOMIC_RELAXED);
    entry->data = prim;
    trace_mem("[rpi] [addr %lx] [size %d] [pc %lx] [index %d] [id %ld]\n", addr, size, pc, entry->shared_index, prim->access_id);
}

bool is_valid_address(target_ulong addr) {
    if (g_snapshot.pages == NULL) {
        trace_mem("ERROR! No valid pages\n");
        return false;
    }
    target_ulong page = addr & SNAPSHOT_PAGE_MASK;
    SnapshotPageInfo *info = g_hash_table_lookup(g_snapshot.pages, &page);
    if (info != NULL) {
        // Valid only if it has write permission
        return (info->perms & PAGE_WRITE) != 0;
    }
    return false;
}

// static GHashTable *get_pointer_access_table(void) {
//     if (g_pointer_access == NULL) {
//         g_pointer_access = g_hash_table_new_full(g_int64_hash, g_int64_equal, NULL, g_free);
//     }
//     return g_pointer_access;
// }

// static void access_pointer(target_ulong addr, target_ulong value, bool is_read) {
//     GHashTable *pointer_access = get_pointer_access_table();
//     if (is_read) {
//         trace_mem("%lx\n", (uintptr_t)pointer_access);
//     }
// }

static GArray *get_pending_allocs(void) {
    if (pending_allocs == NULL) {
        pending_allocs = g_array_new(FALSE, FALSE, sizeof(PendingAlloc));
    }
    return pending_allocs;
}

void snapshot_trace_pending_allocs(target_ulong size, target_ulong pc) {
    GArray *stack = get_pending_allocs();
    PendingAlloc alloc = {size, pc};
    g_array_append_val(stack, alloc);
    trace_mem("[alloc] [temp] [size %lx] [pc %lx]\n", size, pc);
}

PendingAlloc snapshot_trace_get_pending_allocs(target_ulong pc) {
    GArray *stack = get_pending_allocs();
    PendingAlloc result = {0, 0};
    if (stack->len == 0) {
        // This should not happen
        return result;
    }
    result = g_array_index(stack, PendingAlloc, stack->len - 1);
    if (result.pc != pc) {
        result = (PendingAlloc){0, 0};
        return result;
    }
    g_array_set_size(stack, stack->len - 1);
    return result;
}

static gint compare_regions(gconstpointer a, gconstpointer b, gpointer user_data) {
    const SnapshotMemRegion *ra = (const SnapshotMemRegion *)a;
    const SnapshotMemRegion *rb = (const SnapshotMemRegion *)b;
    if (ra->base < rb->base) return -1;
    if (ra->base > rb->base) return 1;
    return 0;
}

static gint compare_regions_ptr(gconstpointer a, gconstpointer b) {
    const SnapshotMemRegion *ra = *(const SnapshotMemRegion **)a;
    const SnapshotMemRegion *rb = *(const SnapshotMemRegion **)b;
    if (ra->base < rb->base) return -1;
    if (ra->base > rb->base) return 1;
    return 0;
}

static int check_addr_in_region(SnapshotMemRegion *mr, target_ulong addr) {
    if (mr->is_stack) {
        /* Stack grows downward: region is [base - size, base]. */
        if (mr->size != 0) {
            if (addr > mr->base) {
                return 1;
            }
            if (addr + mr->size >= mr->base) {
                return 0;
            }
            return -1;
        }

        /* size unknown: accept a lazy window below (or at) base */
        if (mr->base >= addr && mr->base - addr <= SNAPSHOT_STACK_LAZY_WINDOW) {
            return 0;
        }
        return (addr > mr->base) ? 1 : -1;
    }
    if (mr->base + mr->size < addr) return -1;
    if (mr->base > addr) return 1;
    return 0;
}

static void init_mr_manager(void) {
    if (mr_manager.stack_data == NULL) {
        mr_manager.stack_data = g_array_new(FALSE, FALSE, sizeof(SnapshotMemRegion *));
    }
    if (mr_manager.heap_data == NULL) {
        mr_manager.heap_data = g_tree_new_full(
            (GCompareDataFunc)compare_regions,
            NULL,
            g_free,
            NULL
        );
        mr_manager.heap_cache_index = 0;
        for (int i = 0; i < SNAPSHOT_MEM_REG_CACHE; i++) {
            mr_manager.heap_cache[i] = NULL;
        }
    }
    if (mr_manager.global_data == NULL) {
        mr_manager.global_data = g_array_new(FALSE, FALSE, sizeof(SnapshotMemRegion *));
        mr_manager.global_cache_index = 0;
        for (int i = 0; i < SNAPSHOT_MEM_REG_CACHE; i++) {
            mr_manager.global_cache[i] = NULL;
        }
    }
}

static int mr_manager_search_cache(SnapshotMemRegion **mr_cache, target_ulong addr) {
    for (int i = 0; i < SNAPSHOT_MEM_REG_CACHE; i++) {
        SnapshotMemRegion *mr = mr_cache[i];
        if (mr != NULL && check_addr_in_region(mr, addr) == 0) {
            return i;
        }
    }
    return -1;
}

static int mr_manager_new_cache_index(int prev) {
    return (prev + 1) % SNAPSHOT_MEM_REG_CACHE;
}

static int mr_manager_search_cache_exact(SnapshotMemRegion **mr_cache, SnapshotMemRegion *query) {
    for (int i = 0; i < SNAPSHOT_MEM_REG_CACHE; i++) {
        SnapshotMemRegion *mr = mr_cache[i];
        if (mr != NULL && compare_regions(mr, query, NULL) == 0) {
            return i;
        }
    }
    return -1;
}

static void mr_manager_update_cache(SnapshotMemRegion **mr_cache, SnapshotMemRegion *target, int index) {
    if (index >= 0 && index < SNAPSHOT_MEM_REG_CACHE && mr_cache != NULL) {
        mr_cache[index] = target;
    }
}

static SnapshotMemRegion *mr_manager_get_cache(SnapshotMemRegion **mr_cache, int index) {
    if (index >= 0 && index < SNAPSHOT_MEM_REG_CACHE && mr_cache != NULL) {
        return mr_cache[index];
    }
    return NULL;
}

static void mr_manager_update_region(SnapshotMemRegion *old_mr, SnapshotMemRegion *new_mr) {
    if (new_mr->is_stack) {
        // For stack, just update size
        if (old_mr->base == 0) {
            *old_mr = *new_mr;
            old_mr->size += SNAPSHOT_STACK_LAZY_WINDOW;
            trace_mem("[stack] [lazy init] [base %lx] [size %lx]\n", old_mr->base, old_mr->size);
            return;
        }
        if (old_mr->base > new_mr->base) {
            if (old_mr->size < (old_mr->base - new_mr->base + SNAPSHOT_STACK_LAZY_WINDOW)) {
                old_mr->size = (old_mr->base - new_mr->base + SNAPSHOT_STACK_LAZY_WINDOW);
                trace_mem("[stack] [lazy update] [base %lx] [size %lx]\n", old_mr->base, old_mr->size);
            }
        }
        return;
    }
    
    if (old_mr->size == 0) {
        *old_mr = *new_mr;
        return;
    }
    // Update base, size
    if (old_mr->base > new_mr->base) {
        old_mr->size += (old_mr->base - new_mr->base);
        old_mr->base = new_mr->base;
    } else if (old_mr->base + old_mr->size < new_mr->base + new_mr->size) {
        old_mr->size = (new_mr->base + new_mr->size) - old_mr->base;
    }
}

static void mr_manager_heap_insert(SnapshotMemRegion *mr) {
    g_tree_insert(mr_manager.heap_data, mr, mr);
}

static void mr_manager_heap_remove(SnapshotMemRegion *query) {
    // Remove from cache
    int query_result = SNAPSHOT_MEM_REG_CACHE;
    while (query_result >= 0) {
        query_result = mr_manager_search_cache_exact(mr_manager.heap_cache, query);
        mr_manager_update_cache(mr_manager.heap_cache, NULL, query_result);
    }
    
    // Remove from heap_data
    if (!g_tree_remove(mr_manager.heap_data, query)) {
        trace_mem("[free] [error] [base %lx] [pc %lx] not exist\n", query->base, query->pc);
    } else {
        trace_mem("[free] [done] [base %lx] [pc %lx]\n", query->base, query->pc);
    }
}

static gint search_region(gconstpointer a, gconstpointer b) {
    const SnapshotMemRegion *region = (const SnapshotMemRegion *)a;
    const target_ulong addr = *(const target_ulong *)b;
    if (addr < region->base) return 1;
    if (addr >= region->base + region->size) return -1;
    return 0;
}

static SnapshotMemRegion *mr_manager_heap_search(target_ulong addr) {
    int query_result = mr_manager_search_cache(mr_manager.heap_cache, addr);
    SnapshotMemRegion *mr = mr_manager_get_cache(mr_manager.heap_cache, query_result);
    // Cache miss
    if (mr == NULL) {
        mr = g_tree_search(mr_manager.heap_data, (GCompareFunc)search_region, &addr);
    }
    if (mr == NULL) {
        trace_mem("[mr] [heap] [error] failed to search region for [addr %lx]\n", addr);
        return NULL;
    }
    // Update cache
    int new_cache_index = mr_manager_new_cache_index(mr_manager.heap_cache_index);
    mr_manager_update_cache(mr_manager.heap_cache, mr, new_cache_index);
    mr_manager.heap_cache_index = new_cache_index;
    return mr;
}

void snapshot_trace_alloc(target_ulong base, target_ulong size, target_ulong pc) {
    trace_mem("[alloc] [start] [base %lx] [size %lx] [pc %lx]\n", base, size, pc);
    SnapshotMemRegion *obj = g_new(SnapshotMemRegion, 1);
    obj->is_heap = true;
    obj->is_stack = false;
    obj->base = base;
    obj->size = size;
    obj->pc = pc;
    mr_manager_heap_insert(obj);
}

void snapshot_trace_free(target_ulong base, target_ulong pc) {
    trace_mem("[free] [start] [base %lx] [pc %lx]\n", base, pc);
    SnapshotMemRegion query;
    query.base = base;
    query.pc = pc;
    mr_manager_heap_remove(&query);
}

static SnapshotMemRegion *mr_manager_stack_search(target_ulong addr) {
    // int query_result = mr_manager_search_cache(mr_manager.stack_cache, addr);
    // SnapshotMemRegion *mr = mr_manager_get_cache(mr_manager.stack_cache, query_result);
    // if (mr != NULL) {
    //     return mr;
    // }
    trace_mem("[mr] [stack] [search] [addr %lx]\n", addr);
    SnapshotMemRegion *mr = NULL;
    GArray *stack = mr_manager.stack_data;
    for (ssize_t i = stack->len - 1; i >= 0; i--) {
        SnapshotMemRegion* tmp = g_array_index(stack, SnapshotMemRegion *, i);
        if (tmp == NULL) continue;
        if (check_addr_in_region(tmp, addr) == 0) {
            mr = tmp;
            break;
        }
    }
    if (mr != NULL) {
        // Update cache
        // int new_cache_index = mr_manager_new_cache_index(mr_manager.stack_cache_index);
        // mr_manager_update_cache(mr_manager.stack_cache, mr, new_cache_index);
        // mr_manager.stack_cache_index = new_cache_index;
        return mr;
    }
    trace_mem("[mr] [stack] [error] failed to search region for [addr %lx]\n", addr);
    return NULL;
}

void snapshot_trace_stack_push(target_ulong sp, target_ulong pc) {
    if (mr_manager.stack_data == NULL) {
        init_mr_manager();
    }
    /* Fix size of the previous frame lazily using the new stack top */
    trace_mem("[stack] [ipush] [sp %lx] [pc %lx]\n", sp, pc);
    if (mr_manager.stack_data->len > 0) {
        SnapshotMemRegion *prev = g_array_index(mr_manager.stack_data, SnapshotMemRegion *, mr_manager.stack_data->len - 1);
        if (prev == NULL) {
            trace_mem("[stack] [push-error] previous frame is NULL!\n");
            return;
        }
        if (sp < prev->base) {
            target_ulong new_size = prev->base - sp;
            if (new_size > prev->size) {
                // prev->size = new_size;
                mr_manager_update_region(&mr_manager.stack_region, prev);
            }
        }
    }

    SnapshotMemRegion *mr = g_new(SnapshotMemRegion, 1);
    mr->is_heap = false;
    mr->is_stack = true;
    mr->base = sp;
    mr->size = 0;
    mr->pc = pc;
    g_array_append_val(mr_manager.stack_data, mr);
    mr_manager_update_region(&mr_manager.stack_region, mr);
    trace_mem("[stack] [push] [sp %lx] [size %lx] [pc %lx] [depth %d] [sr-base %lx] [sr-size %lx]\n", sp, mr->size, pc, mr_manager.stack_data->len, mr_manager.stack_region.base, mr_manager.stack_region.size);
}

void snapshot_trace_stack_pop(target_ulong sp) {
    if (mr_manager.stack_data == NULL) {
        init_mr_manager();
    }
    trace_mem("[stack] [ipop] [sp %lx]\n", sp);
    GArray *stack = mr_manager.stack_data;
    if (stack->len == 0) {
        trace_mem("[stack] [pop-error] [sp %lx] [depth %d] empty stack!\n", sp, stack->len);
        return;
    }
    for (ssize_t i = stack->len - 1; i >= 0; i--) {
        SnapshotMemRegion *mr = g_array_index(stack, SnapshotMemRegion *, i);
        if (mr == NULL) continue;
        if (check_addr_in_region(mr, sp) == 0) {
            g_array_remove_index(stack, i);
            trace_mem("[stack] [pop] [sp %lx] [base %lx] [pc %lx] [depth %d]\n",
                      sp, mr->base, mr->pc, stack->len);
            g_free(mr);
            return;
        }
    }
    trace_mem("[stack] [pop-error] [sp %lx] [depth %d] not found!\n", sp, stack->len);
}

void snapshot_trace_global_add(target_ulong base, target_ulong size, target_ulong pc, const char *name) {
    if (mr_manager.global_data == NULL) {
        init_mr_manager();
    }
    SnapshotMemRegion *mr = g_new(SnapshotMemRegion, 1);
    mr->is_heap = false;
    mr->is_stack = false;
    mr->base = base;
    mr->size = size;
    mr->pc = pc;

    g_array_append_val(mr_manager.global_data, mr);
    
    g_array_sort(mr_manager.global_data, (GCompareFunc)compare_regions_ptr);
    
    mr_manager_update_region(&mr_manager.global_region, mr);
    trace_mem("[global] [add] [base %lx] [size %lx] [name %s] [pc %lx]\n", 
              base, size, name ? name : "unknown", pc);
}

static SnapshotMemRegion *mr_manager_global_search(target_ulong addr) {
    trace_mem("[mr] [global] [search] [addr %lx]\n", addr);

    int query_result = mr_manager_search_cache(mr_manager.global_cache, addr);
    SnapshotMemRegion *mr = mr_manager_get_cache(mr_manager.global_cache, query_result);
    if (mr != NULL) {
        return mr;
    }

    GArray *globals = mr_manager.global_data;
    if (globals->len == 0) return NULL;

    int low = 0;
    int high = globals->len - 1;
    SnapshotMemRegion *found = NULL;

    // Binary search
    while (low <= high) {
        int mid = low + (high - low) / 2;
        SnapshotMemRegion *mr = g_array_index(globals, SnapshotMemRegion *, mid);
        
        int res = check_addr_in_region(mr, addr);
        if (res == 0) {
            found = mr;
            break;
        } else if (res < 0) { // mr->base + size < addr
            low = mid + 1;
        } else { // mr->base > addr
            high = mid - 1;
        }
    }

    if (found) {
        int next_cache_idx = mr_manager_new_cache_index(mr_manager.global_cache_index);
        mr_manager_update_cache(mr_manager.global_cache, found, next_cache_idx);
        mr_manager.global_cache_index = next_cache_idx;
        return found;
    }

    trace_mem("[mr] [global] [error] failed to search region for [addr %lx]\n", addr);
    return NULL;
}

SnapshotMemRegion *snapshot_mem_region_search(target_ulong addr) {
    // Determine region by address
    if (check_addr_in_region(&mr_manager.stack_region, addr) == 0) {
        trace_mem("[mr] [search] [stack] [addr %lx]\n", addr);
        return mr_manager_stack_search(addr);
    } else if (check_addr_in_region(&mr_manager.global_region, addr) == 0) {
        trace_mem("[mr] [search] [global] [addr %lx]\n", addr);
        return mr_manager_global_search(addr);
    } else {
        trace_mem("[mr] [search] [heap] [addr %lx]\n", addr);
        return mr_manager_heap_search(addr);
    }
}

bool snapshot_is_taken(void) {
    // return g_snapshot.is_snapshot_taken;
    return true;
}

void snapshot_init(void) {
    memset(&mr_manager, 0, sizeof(SnapshotMemRegionManager));
    init_mr_manager();
    memset(&g_snapshot, 0, sizeof(SnapshotState));
    g_snapshot.pages = g_hash_table_new_full(g_int64_hash, g_int64_equal, g_free, g_free);
    g_snapshot.is_snapshot_taken = false;
    // g_snapshot.cpu_state = malloc(sizeof(CPUArchState));
    // memset(g_snapshot.cpu_state, 0, sizeof(CPUArchState));
    size_t shm_size = sizeof(SharedTraceData);
    shared_trace_data = mmap(NULL, shm_size, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (shared_trace_data == MAP_FAILED) {
        perror("mmap shared memory failed");
        exit(1);
    }
    memset(shared_trace_data, 0, shm_size);
}

static int walk_memory_cb(void *priv, target_ulong start, target_ulong end,
                          unsigned long flags) {
    if (flags & PAGE_READ) {
        target_ulong addr;
        for (addr = start; addr < end; addr += SNAPSHOT_PAGE_SIZE) {
            SnapshotPageInfo *info = g_malloc0(sizeof(SnapshotPageInfo));
            info->addr = addr;
            info->perms = flags;
            info->data = g_malloc(SNAPSHOT_PAGE_SIZE);
            
            void *host_addr = g2h(addr);
            // memcpy(info->data, host_addr, SNAPSHOT_PAGE_SIZE);

            target_ulong *key = g_malloc(sizeof(target_ulong));
            *key = addr;
            g_hash_table_insert(g_snapshot.pages, key, info);
            trace_mem("[snapshot] [memwalk] [addr %lx] [perms %ld] [host %lx]\n", (uint64_t)addr, flags, (uint64_t)host_addr);
        }
    }
    return 0;
}

void snapshot_save(void) {
    if (g_snapshot.pages == NULL) snapshot_init();
    if (g_snapshot.is_snapshot_taken) return;
    trace_mem("[snapshot] [mem] [start]\n");
    // CPU state
    // if (g_snapshot.cpu_state) {
    //     trace_mem("[snapshot] [cpu] [at %lx] [size %ld]\n", (uintptr_t)cpu, sizeof(CPUArchState));
    //     memcpy(g_snapshot.cpu_state, cpu, sizeof(CPUArchState));
    // }
    // Memory
    walk_memory_regions(&g_snapshot, walk_memory_cb);

    g_snapshot.start_brk = target_brk;
    g_snapshot.start_mmap = mmap_next_start;
    
    g_snapshot.is_snapshot_taken = true;
    trace_mem("[snapshot] [result] [brk %llx] [mmap %llx] [pages %d]\n", (long long int)target_brk, (long long int)mmap_next_start, g_hash_table_size(g_snapshot.pages));
}

void snapshot_write_access(SnapshotMemAccess *mem_access) {
    if (!forkserver_installed) return;
    uint64_t addr = mem_access->addr;
    uint64_t size = mem_access->size;
    if (size == sizeof(target_ulong)) {
        target_ulong target;
        memcpy(&target, mem_access->target, sizeof(target_ulong));
        if (is_valid_address(target)) {
            // Trace?
        }
    }
    // target_ulong start = addr & SNAPSHOT_PAGE_MASK;
    // target_ulong end = (addr + size - 1) & SNAPSHOT_PAGE_MASK;
    trace_mem("[snapshot] [waccess] [mem] [addr %lx] [size %ld]\n", addr, size);
}

void snapshot_read_access(SnapshotMemAccess *mem_access) {
    if (!forkserver_installed) return;
    uintptr_t addr = mem_access->addr;
    uintptr_t size = mem_access->size;
    // target_ulong start = addr & SNAPSHOT_PAGE_MASK;
    // target_ulong end = (addr + size - 1) & SNAPSHOT_PAGE_MASK;
    bool is_value_pointer = false;
    if (size == sizeof(target_ulong)) {
        target_ulong target;
        memcpy(&target, mem_access->target, sizeof(target_ulong));
        if (is_valid_address(target)) {
            // Add to pointer
            add_read_access_pointer(addr, target, mem_access->pc);
            is_value_pointer = true;
        }
    }
    if (!is_value_pointer) {
        if (mem_access->symbolic_value) {
            // Tainted value
            add_read_access_primitive(addr, size, mem_access->pc);
        }
    }
    trace_mem("[snapshot] [raccess] [mem] [addr %lx] [size %ld]\n", addr, size);
}

// Unused: replaced by fork server
// void snapshot_restore(CPUArchState *cpu) {
//     // CPU state
//     restoring_to_snapshot = true;
//     if (g_snapshot.cpu_state) {
//         trace_mem("[snapshot] [restore-cpu]\n");
//         memcpy(cpu, g_snapshot.cpu_state, sizeof(CPUArchState));
//     }
    
//     SnapshotTLS *tls = get_tls_w();
//     // mmap
//     while (g_snapshot.new_mappings != NULL) {
//         SnapshotMapping *map = (SnapshotMapping *)g_snapshot.new_mappings->data;
//         // Remove new mmap
//         trace_mem("[snapshot] [restore] [munmap] [addr %lx]\n", map->start);
//         target_munmap(map->start, map->len);
//         g_free(map);
//         g_snapshot.new_mappings = g_list_delete_link(g_snapshot.new_mappings, g_snapshot.new_mappings);
//     }

//     // brk
//     // The heap has shrunk - restore missing pages
//     if (target_brk < g_snapshot.start_brk) {
//         target_ulong aligned_new_brk = (target_brk + (SNAPSHOT_PAGE_SIZE - 1)) & (~(SNAPSHOT_PAGE_SIZE - 1));
//         trace_mem("[snapshot] [restore] [brk-s] [snap %lx] [new %lx] [aligned %lx] [size %lx]\n", target_brk, g_snapshot.start_brk, aligned_new_brk, g_snapshot.start_brk - aligned_new_brk);
//         abi_long brk_ret = do_brk(g_snapshot.start_brk);
//         if (brk_ret != g_snapshot.start_brk) {
//             trace_mem("[snapshot] [restore] [brk-s-err] [grow-failed %lx]\n", brk_ret);
//         }
//     } else if (target_brk > g_snapshot.start_brk) { // Remove new allocations
//         trace_mem("[snapshot] [restore] [brk-l] [snap %lx] [new %lx]\n", target_brk, g_snapshot.start_brk);
//     }

//     // 3. Dirty Page
//     GHashTableIter iter;
//     gpointer key, value;
//     g_hash_table_iter_init(&iter, tls->dirty_pages);

//     while (g_hash_table_iter_next(&iter, &key, &value)) {
//         target_ulong addr = *(target_ulong*)key;
        
//         SnapshotPageInfo *info = g_hash_table_lookup(g_snapshot.pages, &addr);
//         if (info) {
//             // memcpy with original data
//             void *host_addr = g2h(addr);
            
//             // mprotect(host_addr, SNAPSHOT_PAGE_SIZE, PROT_READ | PROT_WRITE); 
//             memcpy(host_addr, info->data, SNAPSHOT_PAGE_SIZE);
//             trace_mem("[snapshot] [restore] [dirty] [addr %lx]\n", (uintptr_t)addr);
//         } else {
//             // void *host_addr = g2h(addr);
//             // memset(host_addr, 0, SNAPSHOT_PAGE_SIZE);
//             trace_mem("[snapshot] [restore] [dirty-unknown] [addr %lx]\n", (uintptr_t)addr);
//         }
//     }

//     g_hash_table_remove_all(tls->dirty_pages);
//     for(int i=0; i<4; i++) tls->access_cache[i] = -1;
    
//     trace_mem("[snapshot] [restore] [fin]\n");
//     fflush(stderr);
// }

// Syscall Hook
void snapshot_syscall(uintptr_t syscall_no, uintptr_t syscall_arg0,
                      uintptr_t syscall_arg1, uintptr_t syscall_arg2,
                      uintptr_t syscall_arg3, uintptr_t syscall_arg4,
                      uintptr_t syscall_arg5, uintptr_t syscall_arg6,
                      uintptr_t ret_val) {
    switch (syscall_no) {
    case TARGET_NR_read:
    case TARGET_NR_pread64: // read from file (write to buffer)
        // read(fd, buf, count) -> read count
        if ((long)ret_val > 0) {
            // addr
            SnapshotMemAccess mem_access = {
                .symbolic_addr = false,
                .symbolic_value = false,
                .addr = syscall_arg1,
                .pc = 0,
                .target = {0},
                .ptr = NULL,
                .size = ret_val
            };
            if (ret_val <= 8) {
                void *buf = g2h(syscall_arg1);
                memcpy(mem_access.target, buf, ret_val);
            }
            snapshot_write_access(&mem_access);
        }
        break;
    case TARGET_NR_write:
    case TARGET_NR_pwrite64: // write to file (read from buffer)
        if ((long)ret_val > 0) {
            SnapshotMemAccess mem_access = {
                .symbolic_addr = false,
                .symbolic_value = false,
                .addr = syscall_arg1,
                .pc = 0,
                .target = {0},
                .ptr = NULL,
                .size = ret_val
            };
            if (ret_val <= 8) {
                void *buf = g2h(syscall_arg1);
                memcpy(mem_access.target, buf, ret_val);
            }
            snapshot_read_access(&mem_access);
        }
        break;
    case TARGET_NR_readlinkat: // Read path from symbolic link
        // readlinkat(dirfd, pathname, buf, bufsize)
        // snapshot_write_access(syscall_arg2, syscall_arg3);
#if defined(TARGET_NR_futex)
    case TARGET_NR_futex: // Fast user mutex
        // futex(uaddr, op, val, timeout)
        // snapshot_write_access(syscall_arg0, syscall_arg3);
        break;
#endif
#if defined(TARGET_NR_newfstatat)
    case TARGET_NR_newfstatat: // Return file status as stat
        // newfstatat(dirfd, pathname, statbuf, flags)
        // snapshot_write_access(syscall_arg2, 4096);
        break;
#endif
#if defined(TARGET_NR_fstatat64)
    case TARGET_NR_fstatat64:
        // snapshot_write_access(syscall_arg2, 4096);
        break;
#endif
    case TARGET_NR_statfs:
    case TARGET_NR_fstat:
    case TARGET_NR_fstatfs:
        // fstat(fd, statbuf)
        // snapshot_write_access(syscall_arg1, 4096);
        break;
    case TARGET_NR_getrandom: {
        // getrandom(buf, buflen, flags)
        SnapshotMemAccess mem_access = {
            .symbolic_addr = false,
            .symbolic_value = false,
            .addr = syscall_arg0,
            .pc = 0,
            .target = {0},
            .ptr = NULL,
            .size = syscall_arg1
        };
        if (syscall_arg1 <= 8) {
            void *buf = g2h(syscall_arg0);
            memcpy(mem_access.target, buf, syscall_arg1);
        }
        snapshot_write_access(&mem_access);
        break;
    }
    case TARGET_NR_brk: // heap adjustment
        // brk(new_brk_addr)
        // Handled in snapshot_restore
        trace_mem("New brk %lx received.\n", syscall_arg0);
        break;
    // System call that changes heap shape:
    case TARGET_NR_mmap: // Memory map to file
        // mmap(addr, size, prot, flags, fd, offset) -> mapped addr
        snapshot_add_mapping(ret_val, syscall_arg1);
        break;
    case TARGET_NR_mremap: // memory remap
        // mremap(old_addr, old_size, new_size, flags, new_addr) -> new addr
        // snapshot_remove_mapping(syscall_arg0, syscall_arg1);
        snapshot_add_mapping(ret_val, syscall_arg2);
        break;
    case TARGET_NR_munmap: // unmap
        // munmap(addr, length)
        // snapshot_remove_mapping(syscall_arg0, syscall_arg1);
        break;
    case TARGET_NR_mprotect: // permission
        // mprotect(start, len, prot)
        // BINRADAR TODO: implement
        break;
    default:
        break;
    }
}

// Syscall Hook: munmap (linux-user/syscall.c do_syscall1())
// Do not unmap if any page in the range is in the snapshot
int snapshot_is_unmap_allowed(target_ulong addr, target_ulong len) {
    return 1;
    target_ulong end = addr + len;
    for (target_ulong p = addr; p < end; p += SNAPSHOT_PAGE_SIZE) {
        if (g_hash_table_contains(g_snapshot.pages, &p)) {
            return 0; // False
        }
    }
    return 1; // True
}


void snapshot_add_mapping(target_ulong addr, target_ulong len) {
    if (addr == -1) return;
    SnapshotMapping *map = g_malloc(sizeof(SnapshotMapping));
    map->start = addr;
    map->len = len;
    g_snapshot.new_mappings = g_list_prepend(g_snapshot.new_mappings, map);
    trace_mem("[snapshot] [mmap] [add] [addr %lx] [len %ld]\n", addr, len);
}

void snapshot_remove_mapping(target_ulong addr, target_ulong len) {
    for (GList *l = g_snapshot.new_mappings; l != NULL; l = l->next) {
        SnapshotMapping *map = (SnapshotMapping *)l->data;
        g_free(map);
        trace_mem("[snapshot] [munmap] [remove] [addr %lx]\n", addr);
        return;
    }
}

void snapshot_fork_setup(void) {
    trace_mem("[forkserver] [setup]\n");
}

// Modify guest program's state base on mod_manager (check analyze_collected_data)
// Called after fork to keep clean initial state
static void snapshot_modify_memory(void) {
    if (mod_manager == NULL) {
        // Initial run: no modification
        return;
    }
    // Select one from modifications
    GArray *mods = mod_manager->current;
    if (mods == NULL) {
        trace_mem("ERROR: empty modification\n");
        exit(1);
    }
    for (int i = 0; i < mods->len; i++) {
        SingleModification mod = g_array_index(mods, SingleModification, i);
        void *target_addr_h = g2h(mod.addr);
        memcpy(target_addr_h, mod.target, mod.size);
        trace_mem("[mod] [addr %lx] [size %ld] [total %d]\n", mod.addr, mod.size, g_queue_get_length(mod_manager->modifications));
    }
}

#ifdef SNAPSHOT_DEBUG
static void snapshot_sig_handler(int sig, siginfo_t *si, void *ctx) {
    CPUState *cpu = thread_cpu;
    CPUArchState *env = cpu ? cpu->env_ptr : NULL;
    snapshot_record_guest_crash(env, 0, sig, si ? si->si_code : 0, 0, si ? (uintptr_t)si->si_addr : 0, "host crashed!!");
    void *frames[SNAPSHOT_BT_DEPTH];
    int n = backtrace(frames, SNAPSHOT_BT_DEPTH);
    dprintf(STDERR_FILENO, "[forkserver-child] fata signal %d (%s) addr=%p\n", sig, strsignal(sig), si ? si->si_addr : NULL);
    backtrace_symbols_fd(frames, n, STDERR_FILENO);
    _exit(128 + sig);
}

static void snapshot_install_crash_handler(void) {
    struct sigaction sa = {
        .sa_sigaction = snapshot_sig_handler,
        .sa_flags = SA_SIGINFO | SA_RESETHAND
    };
    sigemptyset(&sa.sa_mask);
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);
    sigaction(SIGABRT, &sa, NULL);
}
#endif

static int compare_prim_id_desc(const void *a, const void *b) {
    const PrimitiveAccess *pa = (const PrimitiveAccess *)a;
    const PrimitiveAccess *pb = (const PrimitiveAccess *)b;
    
    if (pa->access_id > pb->access_id) return -1;
    if (pa->access_id < pb->access_id) return 1;
    return 0;
}

static int compare_ptr_id_desc(const void *a, const void *b) {
    const PointerAccess *pa = (const PointerAccess *)a;
    const PointerAccess *pb = (const PointerAccess *)b;
    
    if (pa->access_id > pb->access_id) return -1;
    if (pa->access_id < pb->access_id) return 1;
    return 0;
}

static void flip_bits(uint8_t *target, int size) {
    for (int i = 0; i < size; i++) {
        target[i] = ~target[i];
    }
}

// In parent process, called after child execution
// Return 1: halt execution
static int analyze_collected_data(void) {
    if (shared_trace_data == NULL) {
        trace_mem("Snapshot init error: shared_trace_data is null\n");
        exit(1);
    }
    // Analyze exit reason
    SnapshotExitInfo *exit_info = snapshot_exit_info_ptr();
    if (!exit_info || !exit_info->valid) {
        trace_mem("[analyze] [exit-error] no exit info!!!\n");
        return 1;
    }
    bool is_crash = exit_info->crashed;
    if (is_crash) {
        const char *host_name =
                    (exit_info->host_signal > 0) ? strsignal(exit_info->host_signal) : NULL;
        if (exit_info->target_signal == 0) {
            trace_mem("[analyze] [host-crash] [exit %d] [addr %lx] [reason %s] [name %s] [last %lx] Host crashed!!!\n", exit_info->host_signal, exit_info->host_fault_addr, exit_info->description, host_name ? host_name : "unknown", exit_info->guest_last_translation_block);
            exit(1);
        }
        trace_mem("[analyze] [crash] [exit %d] [target %d] [host %d] [name %s] [fault-addr %lx] [guest-pc %lx] [guest-cs %lx] [si-code %d] [last %lx]\n", exit_info->exit_code, exit_info->target_signal, exit_info->host_signal, host_name ? host_name : "unknown", exit_info->fault_addr, exit_info->guest_pc, exit_info->guest_cs_base, exit_info->si_code, exit_info->guest_last_translation_block);
    } else {
        trace_mem("[analyze] [normal] [exit %d] [guest-pc %lx] [guest-cs %lx] [reason %s] [last %lx]\n", exit_info->exit_code, exit_info->guest_pc, exit_info->guest_cs_base, exit_info->description, exit_info->guest_last_translation_block);
    }
    // Analyze shared_trace_data
    // Sort by access_id
    qsort(shared_trace_data->primitives, shared_trace_data->prim_idx, sizeof(PrimitiveAccess), compare_prim_id_desc);
    qsort(shared_trace_data->pointers, shared_trace_data->ptr_idx, sizeof(PointerAccess), compare_ptr_id_desc);
    // First run: collect all data
    if (mod_manager == NULL) {
        mod_manager = g_new(ModificationManager, 1);
        mod_manager->modifications = g_queue_new();
        mod_manager->done = g_array_new(FALSE, FALSE, sizeof(GArray *));
        mod_manager->current = NULL;
        
        memcpy(&original_exit_info, exit_info, sizeof(SnapshotExitInfo));
        g_read_access_tainted_primitives_original = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        g_read_access_pointers_original = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        g_read_access_tainted_primitives_all = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        g_read_access_pointers_all = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        // TODO: analyze added queries
        Query *query_top = exit_info->next_query;
        for (Query *q = next_query; q < query_top; q++) {
            trace_mem("[analyze] [query] [op %s] [addr %lx]\n", opkind_to_str(q->query->opkind), q->address);
        }
        
        // Create modification list
        for (int i = 0; i < shared_trace_data->prim_idx; i++) {
            PrimitiveAccess *prim = &shared_trace_data->primitives[i];
            PrimitiveAccess *prim_data = g_new(PrimitiveAccess, 1);
            memcpy(prim_data, prim, sizeof(PrimitiveAccess));
            g_hash_table_insert(g_read_access_tainted_primitives_original, GUINT_TO_POINTER(prim_data->addr), prim_data);
            g_hash_table_insert(g_read_access_tainted_primitives_all, GUINT_TO_POINTER(prim_data->addr), prim_data);
            trace_mem("[analyze] [primitive] [index %d] [addr %lx] [size %d] [id %ld]\n", i, prim->addr, prim->size, prim->access_id);
            SingleModification mod = {
                .addr = prim->addr,
                .size = prim->size,
                .target = {0}
            };
            // Get actual value
            if (prim->size <= 8) {
                void *ptr_h = g2h(prim->addr);
                memcpy(mod.target, ptr_h, prim->size);
            }
            // Set to 0, Set to 1, bitflip
            // TODO: better modification methods
            // TODO: multi loc modification
            // TODO: remove partial pointer access (memcpy(target, ptr, 8))
            switch (mod.size) {
                case 1: {
                    uint8_t val = mod.target[0];
                    if (val != 0) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        mod.target[0] = 0;
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    if (val != 1) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        mod.target[0] = 1;
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                    flip_bits(mod.target, mod.size);
                    g_array_append_val(arr, mod);
                    g_queue_push_tail(mod_manager->modifications, arr);
                    break;
                }
                case 2: {
                    uint16_t val;
                    memcpy(&val, mod.target, 2);
                    if (val != 0) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        memset(mod.target, 0, 2);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    if (val != 1) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        uint16_t one = 1;
                        memcpy(mod.target, &one, 2);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                    flip_bits(mod.target, mod.size);
                    g_array_append_val(arr, mod);
                    g_queue_push_tail(mod_manager->modifications, arr);
                    break;
                }
                case 4: {
                    uint32_t val;
                    memcpy(&val, mod.target, 4);
                    if (val != 0) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        memset(mod.target, 0, 4);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    if (val != 1) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        uint32_t one = 1;
                        memcpy(mod.target, &one, 4);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                    flip_bits(mod.target, mod.size);
                    g_array_append_val(arr, mod);
                    g_queue_push_tail(mod_manager->modifications, arr);
                    break;
                }
                case 8: {
                    uint64_t val;
                    memcpy(&val, mod.target, 8);
                    if (val != 0) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        memset(mod.target, 0, 8);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    if (val != 1) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        uint64_t one = 1;
                        memcpy(mod.target, &one, 8);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                    flip_bits(mod.target, mod.size);
                    g_array_append_val(arr, mod);
                    g_queue_push_tail(mod_manager->modifications, arr);
                    break;
                }
                default: {
                    // From real memcpy/memmove (if plt is given) or file write
                    if (mod.size < 8) {
                        flip_bits(mod.target, mod.size);
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    } else {
                        // TODO: fuzzing
                    }
                }
            }
        }
        for (int i = 0; i < shared_trace_data->ptr_idx; i++) {
            PointerAccess *ptr = &shared_trace_data->pointers[i];
            PointerAccess *ptr_data = g_new(PointerAccess, 1);
            memcpy(ptr_data, ptr, sizeof(PointerAccess));
            g_hash_table_insert(g_read_access_pointers_original, GUINT_TO_POINTER(ptr_data->addr), ptr_data);
            g_hash_table_insert(g_read_access_pointers_all, GUINT_TO_POINTER(ptr_data->addr), ptr_data);
            trace_mem("[analyze] [pointer] [index %d] [addr %lx] [target %lx] [id %ld]\n", i, ptr->addr, ptr->target, ptr->access_id);
            SingleModification mod = {
                .addr = ptr->addr,
                .size = sizeof(target_ulong),
                .target = {0}
            };
            // Get actual value
            target_ulong actual_value;
            memcpy(&actual_value, g2h(ptr->addr), sizeof(target_ulong));
            memcpy(mod.target, &actual_value, sizeof(target_ulong));
            // Fix pointer
            if (actual_value != 0) {
                // Set to NULL
                GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                target_ulong null_ptr = 0;
                memcpy(mod.target, &null_ptr, sizeof(target_ulong));
                g_array_append_val(arr, mod);
                g_queue_push_tail(mod_manager->modifications, arr);
            } else {
                // Pointer to new object
                // TODO: recognize null pointer
                // TODO: allocate new page with mmap, cache it and reuse it
            }
        }
        trace_mem("[analyze] [queue] [len %d]\n", g_queue_get_length(mod_manager->modifications));
    } else {
        // Collect only delta, give feedback
        if (original_exit_info.crashed && exit_info->crashed) {
            
        } else if (original_exit_info.crashed && !exit_info->crashed) {
            
        }
        // Append modification list
        for (int i = 0; i < shared_trace_data->prim_idx; i++) {
            PrimitiveAccess *prim = &shared_trace_data->primitives[i];
            if (!g_hash_table_lookup(g_read_access_tainted_primitives_original, GUINT_TO_POINTER(prim->addr))) {
                // TODO: New value
            }
            if (!g_hash_table_lookup(g_read_access_tainted_primitives_all, GUINT_TO_POINTER(prim->addr))) {
                // Found new read
                PrimitiveAccess *prim_data = g_new(PrimitiveAccess, 1);
                memcpy(prim_data, prim, sizeof(PrimitiveAccess));
                g_hash_table_insert(g_read_access_tainted_primitives_all, GUINT_TO_POINTER(prim_data->addr), prim_data);
                trace_mem("[analyze] [new-primitive] [index %d] [addr %lx] [size %d] [id %ld]\n", i, prim->addr, prim->size, prim->access_id);
                SingleModification mod = {
                    .addr = prim->addr,
                    .size = prim->size,
                    .target = {0}
                };
                // Get actual value
                if (prim->size <= 8) {
                    void *ptr_h = g2h(prim->addr);
                    memcpy(mod.target, ptr_h, prim->size);
                }
                // Set to 0, Set to 1, bitflip
                // TODO: better modification methods
                // TODO: multi loc modification
                // TODO: remove partial pointer access (memcpy(target, ptr, 8))
                switch (mod.size) {
                    case 1: {
                        uint8_t val = mod.target[0];
                        if (val != 0) {
                            GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                            mod.target[0] = 0;
                            g_array_append_val(arr, mod);
                            g_queue_push_tail(mod_manager->modifications, arr);
                        }
                        if (val != 1) {
                            GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                            mod.target[0] = 1;
                            g_array_append_val(arr, mod);
                            g_queue_push_tail(mod_manager->modifications, arr);
                        }
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        flip_bits(mod.target, mod.size);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                        break;
                    }
                    case 2: {
                        uint16_t val;
                        memcpy(&val, mod.target, 2);
                        if (val != 0) {
                            GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                            memset(mod.target, 0, 2);
                            g_array_append_val(arr, mod);
                            g_queue_push_tail(mod_manager->modifications, arr);
                        }
                        if (val != 1) {
                            GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                            uint16_t one = 1;
                            memcpy(mod.target, &one, 2);
                            g_array_append_val(arr, mod);
                            g_queue_push_tail(mod_manager->modifications, arr);
                        }
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        flip_bits(mod.target, mod.size);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                        break;
                    }
                    case 4: {
                        uint32_t val;
                        memcpy(&val, mod.target, 4);
                        if (val != 0) {
                            GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                            memset(mod.target, 0, 4);
                            g_array_append_val(arr, mod);
                            g_queue_push_tail(mod_manager->modifications, arr);
                        }
                        if (val != 1) {
                            GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                            uint32_t one = 1;
                            memcpy(mod.target, &one, 4);
                            g_array_append_val(arr, mod);
                            g_queue_push_tail(mod_manager->modifications, arr);
                        }
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        flip_bits(mod.target, mod.size);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                        break;
                    }
                    case 8: {
                        uint64_t val;
                        memcpy(&val, mod.target, 8);
                        if (val != 0) {
                            GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                            memset(mod.target, 0, 8);
                            g_array_append_val(arr, mod);
                            g_queue_push_tail(mod_manager->modifications, arr);
                        }
                        if (val != 1) {
                            GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                            uint64_t one = 1;
                            memcpy(mod.target, &one, 8);
                            g_array_append_val(arr, mod);
                            g_queue_push_tail(mod_manager->modifications, arr);
                        }
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        flip_bits(mod.target, mod.size);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                        break;
                    }
                    default: {
                        // From real memcpy/memmove (if plt is given) or file write
                        if (mod.size < 8) {
                            flip_bits(mod.target, mod.size);
                            GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                            g_array_append_val(arr, mod);
                            g_queue_push_tail(mod_manager->modifications, arr);
                        } else {
                            // TODO: fuzzing
                        }
                    }
                }
            }
        }
        for (int i = 0; i < shared_trace_data->ptr_idx; i++) {
            PointerAccess *ptr = &shared_trace_data->pointers[i];
            if (!g_hash_table_lookup(g_read_access_pointers_original, GUINT_TO_POINTER(ptr->addr))) {
                // New pointer read
            }
            if (!g_hash_table_lookup(g_read_access_pointers_all, GUINT_TO_POINTER(ptr->addr))) {
                // Found new read
                PointerAccess *ptr_data = g_new(PointerAccess, 1);
                memcpy(ptr_data, ptr, sizeof(PointerAccess));
                g_hash_table_insert(g_read_access_pointers_all, GUINT_TO_POINTER(ptr_data->addr), ptr_data);
                trace_mem("[analyze] [new-pointer] [index %d] [addr %lx] [target %lx] [id %ld]\n", i, ptr->addr, ptr->target, ptr->access_id);
                SingleModification mod = {
                    .addr = ptr->addr,
                    .size = sizeof(target_ulong),
                    .target = {0}
                };
                // Get actual value
                target_ulong actual_value;
                memcpy(&actual_value, g2h(ptr->addr), sizeof(target_ulong));
                memcpy(mod.target, &actual_value, sizeof(target_ulong));
                // Fix pointer
                if (actual_value != 0) {
                    // Set to NULL
                    GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                    target_ulong null_ptr = 0;
                    memcpy(mod.target, &null_ptr, sizeof(target_ulong));
                    g_array_append_val(arr, mod);
                    g_queue_push_tail(mod_manager->modifications, arr);
                } else {
                    // Pointer to new object
                    // TODO: recognize null pointer
                    // TODO: allocate new page with mmap, cache it and reuse it
                }
            }
        }
    }
    // Select one modification
    g_array_append_val(mod_manager->done, mod_manager->current);
    mod_manager->current = g_queue_pop_head(mod_manager->modifications);
    // TODO: restore file offset if needed
    if (mod_manager->current == NULL) {
        trace_mem("[analyze] [done] consumed all modifications\n");
        return 1;
    }
    // Clean expr and query added during child execution
    uint8_t *expr_base = (uint8_t *)next_free_expr;
    uint8_t *expr_top  = (uint8_t *)exit_info->next_free_expr;
    if (expr_top > expr_base) {
        memset(next_free_expr, 0, expr_top - expr_base);
    }
    uint8_t *query_base = (uint8_t *)next_query;
    uint8_t *query_top  = (uint8_t *)exit_info->next_query;
    if (query_top > query_base) {
        memset(next_query, 0, query_top - query_base);
    }
    // Finished: reset shared_trace_data
    memset(shared_trace_data, 0, sizeof(SharedTraceData));
    return 0;
}

void snapshot_forkserver(CPUState *cpu) {
    trace_mem("[snapshot] [forkserver] [called %d]\n", forkserver_installed);
    fflush(stderr);
    if (forkserver_installed) return;
    forkserver_installed = true;
    snapshot_save();
    pid_t child_pid;
    // int   t_fd[2];
    unsigned int dropped_rcu = 0;
    while (rcu_reader.depth > 0) {
        rcu_read_unlock();
        dropped_rcu++;
    } 
    
    uint32_t   was_killed;
    uint32_t version = 0x41464c00;
    uint32_t tmp = version ^ 0xffffffff, status2, status = version;
    uint8_t *msg = (uint8_t *)&status;
    uint8_t *reply = (uint8_t *)&status2;
  
    /* Tell the parent that we're alive. If the parent doesn't want
       to talk, assume that we're not running in forkserver mode. */
  
    if (write(FORKSRV_FD + 1, msg, 4) != 4) {
        trace_mem("[snapshot] [forkserver] [error] failed to write to %d %d\n", FORKSRV_FD + 1, status);
        _exit(1);
    }
  
    afl_forksrv_pid = getpid();
  
    if (read(FORKSRV_FD, reply, 4) != 4) {
        trace_mem("[snapshot] [forkserver] [error] fuzzolic not responding to %d\n", FORKSRV_FD); 
        _exit(1);
    }
    if (tmp != status2) {
        trace_mem("wrong forkserver message from fuzzolic.py");
        _exit(1);
    }

    // send welcome message as final message
    if (write(FORKSRV_FD + 1, msg, 4) != 4) { 
        trace_mem("[snapshot] [forkserver] [error] failed to send final handshake to %d %d\n", FORKSRV_FD + 1, status);
        _exit(1);
    }
  
  
    // END forkserver handshake
    trace_mem("[forkserver] [start]\n");
  
    /* All right, let's await orders... */
  
    while (1) {
  
        /* Whoops, parent dead? */
    
        if (read(FORKSRV_FD, &was_killed, 4) != 4) {
            trace_mem("[forkserver] [error] parent (fuzzolic) dead?\n");
            exit(2);
        }
    
        /* Establish a channel with child to grab translation commands. We'll
        read from t_fd[0], child will write to TSL_FD. */

        // if (pipe(t_fd) || dup2(t_fd[1], TSL_FD) < 0) exit(3);
        // close(t_fd[1]);

        child_pid = fork();
        if (child_pid < 0) exit(4);

        if (!child_pid) {
#ifdef SNAPSHOT_DEBUG
            snapshot_install_crash_handler();
#endif
            /* Child process. Close descriptors and run free. */
            snapshot_modify_memory();
            while (dropped_rcu--) {
                rcu_read_lock();
            }
            afl_fork_child = 1;
            close(FORKSRV_FD);
            close(FORKSRV_FD + 1);
            // close(t_fd[0]);
            return;

        }

        /* Parent. */

        // close(TSL_FD);

    
        /* Parent. */
    
        if (write(FORKSRV_FD + 1, &child_pid, 4) != 4) exit(5);
    
        /* Collect translation requests until child dies and closes the pipe. */
    
        // afl_wait_tsl(cpu, t_fd[0]);
    
        /* Get and relay exit status to parent. */
    
        if (waitpid(child_pid, (int *)&status, 0) < 0) exit(6);
        
        // Send return code
        if (write(FORKSRV_FD + 1, &status, 4) != 4) exit(7);
        
        // Child process exit
        int should_halt = analyze_collected_data();
    
        // Send halt signal
        if (write(FORKSRV_FD + 1, &should_halt, 4) != 4) exit(8);
  
    }

}
