#include "snapshot.h"
#include "../tcg/symbolic/symbolic-struct.h"
#include "sbsv.h"
#include "qemu/rcu.h"

#include <stdio.h>
#include <stdint.h>
#include <limits.h>

#define SNAPSHOT_EXIT_DESC_LEN 256
#define SNAPSHOT_BT_DEPTH 64
// #define SNAPSHOT_DEBUG

#ifdef SNAPSHOT_DEBUG
#include <execinfo.h>
#include <signal.h>
#include <unistd.h>
#endif

#include <sys/mman.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <unistd.h>

#define FORKSRV_FD 198

extern target_ulong target_brk;
bool restoring_to_snapshot;
target_ulong binradar_entrypoint = (target_ulong)-1;

extern Query *query_queue;
extern Query *next_query;

static uint64_t binradar_entrypoint_hit_count   = 0;
static uint64_t binradar_forkserver_target_hit_count = 1;
static int      binradar_forkserver_enable      = -1;
static int      binradar_preserve_child_queries = -1;
static int      binradar_solver_mutation_mode   = -1;
static FILE*    binradar_probe_file_fp     = NULL;
static FILE*    binradar_query_window_fp = NULL;
static uint8_t  binradar_query_window_dumped    = 0;

bool forkserver_installed = false;
unsigned char afl_fork_child;
unsigned int  afl_forksrv_pid;

GHashTable *coverage_log_edges_cnt = NULL;
static SnapshotState g_snapshot;

#define SNAPSHOT_MEM_REG_CACHE 4
#define SNAPSHOT_STACK_LAZY_WINDOW (SNAPSHOT_PAGE_SIZE * 16)
typedef struct SnapshotMemRegionManager {
    // Determine region by address
    SnapshotMemRegion stack_region;
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
typedef struct SnapshotExitInfo {
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

typedef struct Modification {
    uint32_t num_mods;
    MutationCandidate *mods;
} Modification;

typedef struct ModificationManager {
    GQueue *modifications; // Queue<Modification *>
    Modification *current;
    GArray *done;    // Array<Modification *>
    GHashTable *mod_maps; // Key: addr, Value: Array<Modification *>
} ModificationManager;

typedef struct PrimitiveAccess {
    int size;
    uintptr_t addr;
    uintptr_t pc;
    uint64_t access_id;
    Expr *expr;
} PrimitiveAccess;

typedef struct PointerAccess {
    uintptr_t addr;
    uintptr_t target;
    uintptr_t pc;
    uint64_t access_id;
    Expr *expr;
} PointerAccess;

typedef struct SharedTraceData {
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

static void snapshot_load_binradar_env(void) {
    if (binradar_forkserver_enable != -1) return;

    binradar_forkserver_enable      = 1;
    binradar_preserve_child_queries = 0;
    binradar_solver_mutation_mode = 0;

    const char* var = getenv("BINRADAR_FORKSERVER_ENABLE");
    if (var) {
        binradar_forkserver_enable = atoi(var) != 0;
    }

    var = getenv("BINRADAR_FORKSERVER_TARGET_HIT_COUNT");
    if (var) {
        uint64_t target = strtoull(var, NULL, 10);
        if (target == ULLONG_MAX) {
            target = 0;
        }
        binradar_forkserver_target_hit_count = target;
    }

    var = getenv("BINRADAR_PRESERVE_CHILD_QUERIES");
    if (var) {
        binradar_preserve_child_queries = atoi(var) != 0;
    }

    const char *probe_file = getenv("BINRADAR_PROBE_FILE");
    if (probe_file && probe_file[0] && binradar_probe_file_fp == NULL) {
        binradar_probe_file_fp = fopen(probe_file, "a");
        if (!binradar_probe_file_fp) {
            trace_mem("[snapshot] [error] failed to open BINRADAR_PROBE_FILE %s for write\n", probe_file);
        } else {
            trace_mem("[snapshot] [probe-file] [file %s]\n", probe_file);
        }
    }

    const char *query_window_file = getenv("BINRADAR_QUERY_WINDOW_FILE");
    if (query_window_file && query_window_file[0] && binradar_query_window_fp == NULL) {
        binradar_query_window_fp = fopen(query_window_file, "w");
        if (!binradar_query_window_fp) {
            trace_mem("[snapshot] [error] failed to open BINRADAR_QUERY_WINDOW_FILE %s for write\n", query_window_file);
        } else {
            trace_mem("[snapshot] [query-window-file] [file %s]\n", query_window_file);
        }
    }
    trace_mem("[snapshot-load-binradar] [forkserver %d] [hit-count %lu] [probe-file %s] [query-window-file %s]\n",
              binradar_forkserver_enable, binradar_forkserver_target_hit_count,
              binradar_probe_file_fp ? probe_file : "null",
              binradar_query_window_fp ? query_window_file : "null");
}

static void snapshot_dump_query_window(Query* q) {
    snapshot_load_binradar_env();
    if (binradar_query_window_dumped || binradar_query_window_fp == NULL) {
        return;
    }

    uint64_t q_idx = GET_QUERY_IDX(q);

    fprintf(binradar_query_window_fp, "[query-window] [pre-target %lu]\n", q_idx);
    fflush(binradar_query_window_fp);
    fsync(fileno(binradar_query_window_fp));
    binradar_query_window_dumped = 1;
}

uint8_t snapshot_on_entrypoint_hit(target_ulong pc) {
    snapshot_load_binradar_env();
    binradar_entrypoint_hit_count += 1;

    trace_mem("[snapshot] [entrypoint-hit] [pc %lx] [count %lu] [target %lu]\n",
              pc, binradar_entrypoint_hit_count,
              binradar_forkserver_target_hit_count);

    if (!binradar_forkserver_enable) return 0;
    if (binradar_forkserver_target_hit_count == 0) return 0;
    return binradar_entrypoint_hit_count == binradar_forkserver_target_hit_count;
}

typedef enum OspreyRoleKind {
    OSPREY_ROLE_UNKNOWN = 0,
    OSPREY_ROLE_SCALAR,
    OSPREY_ROLE_FIELD,
    OSPREY_ROLE_ARRAY_ELEM,
    OSPREY_ROLE_STRUCT_BASE,
    OSPREY_ROLE_ARRAY_START,
} OspreyRoleKind;

typedef enum OspreyTypeKind {
    OSPREY_TYPE_PRIMITIVE,
    OSPREY_TYPE_POINTER,
    OSPREY_TYPE_ARRAY,
    OSPREY_TYPE_STRUCT,
} OspreyTypeKind;

typedef struct OspreyType OspreyType;

typedef struct OspreyStructField {
    int64_t offset;
    uint64_t size;
    char *type_id;
    OspreyType *type;
} OspreyStructField;

struct OspreyType {
    OspreyTypeKind kind;
    char *id;
    bool is_pointer;
    uint64_t size;
    // For pointer: the type it points to
    // For array: the type of the element
    OspreyType *target;
    char *target_type_id; // For temp use before resolve
    union {
        struct {
            char *target_role; // For temp use before resolve
        } pointer_info;
        struct {
            GArray *fields; // OspreyStructField
        } struct_info;
        struct {
            uint64_t count;
        } array_info;
    } meta;
};

typedef struct OspreyObject {
    uint64_t addr;
    uint64_t size;

    OspreyRoleKind role;
    OspreyType *type;
    // For field/array_elem: the struct/array it belongs to; For struct/array: NULL
    struct OspreyObject *parent;
} OspreyObject;


typedef struct MemGraph MemGraph;
typedef struct ObjNode ObjNode;
typedef struct PtrNode PtrNode;
typedef struct PtrEdge PtrEdge;

struct PtrNode {
    bool is_value_pointer;
    uint64_t addr;
    PtrNode *points_to;
    ObjNode *base;
};

struct PtrEdge {
    PtrNode *src;
    PtrNode *dst;
};

struct ObjNode {
    uint64_t addr;
    OspreyObject *obj;
    GArray *outgoing_ptr_edges; // PtrEdge*
};

struct MemGraph {
    GHashTable *ptr_nodes; // addr -> PtrNode
    GHashTable *obj_nodes; // addr -> ObjNode
};

typedef struct OspreyTypeManager {
    GHashTable *type_table; // char* id -> OspreyType*
    GHashTable *obj_addr_to_type; // uint64_t addr -> OspreyObject* (scalar, pointer, array_elem, field)
    GHashTable *addr_to_type; // uint64_t addr -> OspreyObject* (array_start, struct)
    GHashTable *addr_to_type_id; // uint64_t addr -> char* type_id
    MemGraph mem_graph;
} OspreyTypeManager;

static int osprey_type_size(OspreyType *type) {
    if (type == NULL) {
        return 0;
    }
    switch (type->kind) {
        default:
            return 0;
    }
}

static void osprey_type_free(gpointer data) {
    OspreyType *t = (OspreyType *)data;
    g_free(t->id);
    if (t->kind == OSPREY_TYPE_STRUCT) {
        for (guint i = 0; i < t->meta.struct_info.fields->len; i++) {
            OspreyStructField *f = &g_array_index(t->meta.struct_info.fields, OspreyStructField, i);
            g_free(f->type_id);
        }
        g_array_free(t->meta.struct_info.fields, TRUE);
    }
    g_free(t);
}

static void osprey_object_free(gpointer data) {
    OspreyObject *inst = (OspreyObject *)data;
    g_free(inst);
}

static OspreyTypeManager* osprey_type_manager_new(void) {
    OspreyTypeManager *manager = g_new0(OspreyTypeManager, 1);
    manager->type_table = g_hash_table_new_full(g_str_hash, g_str_equal, NULL, osprey_type_free);
    manager->addr_to_type = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, osprey_object_free);
    manager->obj_addr_to_type = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, osprey_object_free);
    manager->addr_to_type_id = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, g_free);
    manager->mem_graph.ptr_nodes = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, g_free);
    manager->mem_graph.obj_nodes = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, g_free);
    return manager;
}

// static void osprey_type_manager_free(OspreyTypeManager *manager) {
//     g_hash_table_destroy(manager->type_table);
//     g_hash_table_destroy(manager->addr_to_type);
//     g_hash_table_destroy(manager->addr_to_type_id);
//     g_free(manager);
// }

static PtrNode *osprey_ptr_node_get(OspreyTypeManager *manager, uint64_t addr, bool create) {
    PtrNode *node = (PtrNode *)g_hash_table_lookup(
        manager->mem_graph.ptr_nodes, GSIZE_TO_POINTER((gsize)addr));
    if (node == NULL && create) {
        node = g_new0(PtrNode, 1);
        node->addr = addr;
        g_hash_table_insert(manager->mem_graph.ptr_nodes,
                            GSIZE_TO_POINTER((gsize)addr), node);
    }
    return node;
}

static ObjNode *osprey_obj_node_get(OspreyTypeManager *manager, uint64_t addr, bool create) {
    ObjNode *node = (ObjNode *)g_hash_table_lookup(
        manager->mem_graph.obj_nodes, GSIZE_TO_POINTER((gsize)addr));
    if (node == NULL && create) {
        node = g_new0(ObjNode, 1);
        node->addr = addr;
        node->outgoing_ptr_edges = g_array_new(FALSE, FALSE, sizeof(PtrEdge *));
        g_hash_table_insert(manager->mem_graph.obj_nodes,
                            GSIZE_TO_POINTER((gsize)addr), node);
    }
    return node;
}

static PtrEdge *osprey_ptr_edge_create(OspreyTypeManager *manager, PtrNode *src, PtrNode *dst) {
    PtrEdge *edge = g_new0(PtrEdge, 1);
    edge->src = src;
    edge->dst = dst;
    if (src->base) {
        g_array_append_val(src->base->outgoing_ptr_edges, edge);
    }
    return edge;
}

static OspreyObject *osprey_object_get(OspreyTypeManager *manager, uint64_t addr, bool create) {
    OspreyObject *obj = (OspreyObject *)g_hash_table_lookup(
        manager->obj_addr_to_type, GSIZE_TO_POINTER((gsize)addr));
    if (obj == NULL && create) {
        obj = g_new0(OspreyObject, 1);
        obj->addr = addr;
        g_hash_table_insert(manager->obj_addr_to_type,
                            GSIZE_TO_POINTER((gsize)addr), obj);
    }
    return obj;
}

static OspreyObject *osprey_address_get(OspreyTypeManager *manager, uint64_t addr, bool create) {
    OspreyObject *obj = (OspreyObject *)g_hash_table_lookup(
        manager->addr_to_type, GSIZE_TO_POINTER((gsize)addr));
    if (obj == NULL && create) {
        obj = g_new0(OspreyObject, 1);
        obj->addr = addr;
        g_hash_table_insert(manager->addr_to_type,
                            GSIZE_TO_POINTER((gsize)addr), obj);
    }
    return obj;
}

static OspreyType *osprey_type_get(OspreyTypeManager *manager, const char *type_id) {
    if (type_id == NULL) {
        return NULL;
    }
    OspreyType *type = (OspreyType *)g_hash_table_lookup(manager->type_table, type_id);
    return type;
}

OspreyTypeManager *g_osprey_type_manager = NULL;

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

const char *snapshot_mem_region_str(SnapshotMemRegion *mr) {
    if (mr == NULL) return "NULL";
    if (mr->is_stack) {
        return "stack";
    } else if (mr->is_heap) {
        return "heap";
    } else {
        return "global";
    }
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

guint coverage_edge_hash(gconstpointer key) {
    const CoverageEdge* edge = (const CoverageEdge*)key;
    guint h1 = g_int64_hash(&edge->from);
    guint h2 = g_int64_hash(&edge->to);
    return h1 ^ (h2 << 1);
}

gboolean coverage_edge_equal(gconstpointer a, gconstpointer b) {
    const CoverageEdge* edge_a = (const CoverageEdge*)a;
    const CoverageEdge* edge_b = (const CoverageEdge*)b;
    return (edge_a->from == edge_b->from) && (edge_a->to == edge_b->to);
}

CoverageEdge* coverage_edge_copy(const CoverageEdge* edge) {
    CoverageEdge *copy = g_new(CoverageEdge, 1);
    copy->from = edge->from;
    copy->to   = edge->to;
    return copy;
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

static void dump_coverage_edge_log(gboolean update) {
    return;
    if (coverage_log_edges_cnt == NULL) return;
    GHashTableIter iter;
    gpointer key, value;
    g_hash_table_iter_init(&iter, coverage_log_edges_cnt);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        CoverageEdge *edge = (CoverageEdge *)key;
        uint64_t *cnt = (uint64_t *)value;
        if (update) {
            trace_mem("[cov] [update] [from %lx] [to %lx] [cnt %lu]\n", edge->from, edge->to, *cnt);
        } else {
            trace_mem("[cov] [base] [from %lx] [to %lx] [cnt %lu]\n", edge->from, edge->to, *cnt);
        }
    }
    if (!update) {
        g_hash_table_destroy(coverage_log_edges_cnt);
        coverage_log_edges_cnt = NULL;
    }
}

void snapshot_record_guest_normal_exit(CPUArchState *cpu_env, int exit_code, const char *reason) {
    SnapshotExitInfo *info = snapshot_exit_info_ptr();
    if (!snapshot_exit_info_should_update(info, false)) return;
    info->valid = 1;
    info->crashed = 0;
    info->exit_code = exit_code;
    snapshot_exit_info_capture(info, cpu_env);
    snapshot_exit_info_set_reason(info, reason ? reason : "normal_exit");
    trace_mem("[snapshot] [exit] [normal] [entrypoint-hit %lu]\n",
              binradar_entrypoint_hit_count);
    dump_coverage_edge_log(true);
}

void snapshot_record_guest_crash(CPUArchState *cpu_env, int target_signal, int host_signal, int si_code, target_ulong fault_addr, uintptr_t host_fault_addr, const char *reason) {
    snapshot_load_binradar_env();
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
    trace_mem("[snapshot] [exit] [crash] [entrypoint-hit %lu]\n",
              binradar_entrypoint_hit_count);
    if (binradar_probe_file_fp) {
        fprintf(binradar_probe_file_fp, "[snapshot] [crash] [hit-count %lu] [reason %s] [guest_pc %lx] [guest_cs_base %lx] [fault_addr %lx] [host_fault_addr %lx]\n",
                binradar_entrypoint_hit_count, buffer, info->guest_pc, info->guest_cs_base, info->fault_addr, info->host_fault_addr);
        fflush(binradar_probe_file_fp);
    }
    dump_coverage_edge_log(true);
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
    ptr->expr = NULL;
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
    prim->expr = NULL;
    entry->data = prim;
    trace_mem("[rpi] [addr %lx] [size %d] [pc %lx] [index %d] [id %ld]\n", addr, size, pc, entry->shared_index, prim->access_id);
}

void snapshot_bind_read_expr(uintptr_t addr, uintptr_t size, Expr *expr) {
    if (!forkserver_installed || expr == NULL) {
        return;
    }

    if (size == sizeof(target_ulong) && g_read_access_pointers != NULL) {
        uintptr_t aligned_addr = addr & ~(uintptr_t)0x07;
        OrderedMapEntry *ptr_entry = ordered_map_lookup(g_read_access_pointers, aligned_addr);
        if (ptr_entry != NULL && ptr_entry->data != NULL) {
            PointerAccess *ptr = (PointerAccess *)ptr_entry->data;
            ptr->expr = expr;
            return;
        }
    }

    if (g_read_access_tainted_primitives != NULL) {
        OrderedMapEntry *entry = ordered_map_lookup(g_read_access_tainted_primitives, addr);
        if (entry != NULL && entry->data != NULL) {
            PrimitiveAccess *prim = (PrimitiveAccess *)entry->data;
            prim->expr = expr;
        }
    }
}

bool is_valid_address(target_ulong addr, bool for_snapshot) {
    if (g_snapshot.pages == NULL) {
        trace_mem("ERROR! No valid pages\n");
        return false;
    }
    if (for_snapshot && g_hash_table_size(g_snapshot.pages) == 0) {
        return false;
    }
    target_ulong page = addr & SNAPSHOT_PAGE_MASK;
    SnapshotPageInfo *info = g_hash_table_lookup(g_snapshot.pages, &page);
    if (info != NULL) {
        if (for_snapshot) {
            // Valid only if it has write permission
            return (info->perms & PAGE_WRITE) != 0;
        } else {
            return true;
        }
    }
    if (!for_snapshot) {
        return page_get_flags(addr) & PAGE_VALID;
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
    mr_manager.stack_region.is_stack = true;
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
    // trace_mem("[mr] [stack] [search] [addr %lx] [depth %d]\n", addr, mr_manager.stack_data->len);
    SnapshotMemRegion *mr = NULL;
    GArray *stack = mr_manager.stack_data;
    for (ssize_t i = stack->len - 1; i >= 0; i--) {
        SnapshotMemRegion* tmp = g_array_index(stack, SnapshotMemRegion *, i);
        if (tmp == NULL) continue;
        if (check_addr_in_region(tmp, addr) == 0) {
            mr = tmp;
            trace_mem("[mr] [stack] [found] [addr %lx] [base %lx] [size %lx] [pc %lx] [depth %d] [full-depth %d]\n",
                      addr, mr->base, mr->size, mr->pc, i + 1, stack->len);
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
    SnapshotMemRegion *mr = NULL;
    if (check_addr_in_region(&mr_manager.stack_region, addr) == 0) {
        trace_mem("[mr] [search] [stack] [addr %lx]\n", addr);
        mr = mr_manager_stack_search(addr);
    } 
    if (mr != NULL) {
        return mr;
    }
    trace_mem("[mr] [search] [global] [addr %lx]\n", addr);
    mr = mr_manager_global_search(addr);
    if (mr != NULL) {
        return mr;
    }

    trace_mem("[mr] [search] [heap] [addr %lx]\n", addr);
    mr = mr_manager_heap_search(addr);
    if (mr != NULL) {
        return mr;
    }
    trace_mem("[mr] [search] [error] no region found for [addr %lx]\n", addr);
    return NULL;
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
    snapshot_dump_query_window(next_query);
    dump_coverage_edge_log(false);
}

void snapshot_write_access(SnapshotMemAccess *mem_access) {
    if (!forkserver_installed) return;
    uint64_t addr = mem_access->addr;
    uint64_t size = mem_access->size;
    if (size == sizeof(target_ulong)) {
        target_ulong target;
        memcpy(&target, mem_access->target, sizeof(target_ulong));
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
        if (is_valid_address(target, true)) {
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
static void mod_manager_init(void) {
    if (mod_manager == NULL) {
        mod_manager = g_new0(ModificationManager, 1);
        mod_manager->modifications = g_queue_new();
        mod_manager->done = g_array_new(FALSE, FALSE, sizeof(Modification *));
        mod_manager->mod_maps = g_hash_table_new(g_direct_hash, g_direct_equal);
        mod_manager->current = NULL;
    }
}


// Called after fork to keep clean initial state
static void snapshot_modify_memory(CPUArchState *cpu_env) {
    if (mod_manager == NULL) {
        // Initial run: no modification
        return;
    }
    // Select one from modifications
    Modification *mod = mod_manager->current;
    if (mod == NULL) {
        trace_mem("ERROR: empty modification\n");
        exit(1);
    }
    for (int i = 0; i < mod->num_mods; i++) {
        MutationCandidate single_mod = mod->mods[i];
        if (single_mod.addr < SNAPSHOT_PAGE_SIZE) {
            // Modify register
            target_ulong reg_value;
            memcpy(&reg_value, single_mod.value, sizeof(target_ulong));
            cpu_env->regs[(size_t)single_mod.addr] = reg_value;
            trace_mem("[mod-reg] [register %ld] [size %ld] [total %d]\n",
                      single_mod.addr,
                      single_mod.size,
                      g_queue_get_length(mod_manager->modifications));
            continue;
        }
        void *target_addr_h = g2h(single_mod.addr);
        memcpy(target_addr_h, single_mod.value, single_mod.size);
        trace_mem("[mod] [addr %lx] [size %ld] [total %d]\n", single_mod.addr, single_mod.size, g_queue_get_length(mod_manager->modifications));
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

static Modification * add_single_modification(MutationCandidate *mod) {
    Modification *modification = g_new(Modification, 1);
    modification->mods = g_new(MutationCandidate, 1);
    modification->num_mods = 1;
    memcpy(&modification->mods[0], mod, sizeof(MutationCandidate));
    return modification;
}

// static void modification_free(Modification *mod) {
//     if (mod) {
//         if (mod->mods) {
//             g_free(mod->mods);
//         }
//         g_free(mod);
//     }
// }

static void add_modification_primitive(GQueue *modifications, MutationCandidate *mod) {
    // Set to 0, Set to 1, bitflip
    // TODO: better modification methods
    // TODO: multi loc modification
    // TODO: remove partial pointer access (memcpy(target, ptr, 8))
    // TODO: verifiy modification using solver
    switch (mod->size) {
        case 1: {
            uint8_t val = mod->value[0];
            if (val != 0) {
                mod->value[0] = 0;
                Modification *modification = add_single_modification(mod);
                g_queue_push_tail(modifications, modification);
            }
            if (val != 1) {
                Modification *modification = add_single_modification(mod);
                modification->mods[0].value[0] = 1;
                g_queue_push_tail(modifications, modification);
            }
            flip_bits(mod->value, mod->size);
            Modification *modification = add_single_modification(mod);
            g_queue_push_tail(modifications, modification);
            break;
        }
        case 2: {
            uint16_t val;
            memcpy(&val, mod->value, 2);
            if (val != 0) {
                Modification *modification = add_single_modification(mod);
                memset(modification->mods[0].value, 0, 2);
                g_queue_push_tail(modifications, modification);
            }
            if (val != 1) {
                Modification *modification = add_single_modification(mod);
                modification->mods[0].value[0] = 1;
                uint16_t one = 1;
                memcpy(mod->value, &one, 2);
                g_queue_push_tail(modifications, modification);
            }
            Modification *modification = add_single_modification(mod);
            flip_bits(modification->mods[0].value, mod->size);
            g_queue_push_tail(modifications, modification);
            break;
        }
        case 4: {
            uint32_t val;
            memcpy(&val, mod->value, 4);
            if (val != 0) {
                Modification *modification = add_single_modification(mod);
                memset(modification->mods[0].value, 0, 4);
                g_queue_push_tail(modifications, modification);
            }
            if (val != 1) {
                Modification *modification = add_single_modification(mod);
                uint32_t one = 1;
                memcpy(modification->mods[0].value, &one, 4);
                g_queue_push_tail(modifications, modification);
            }
            Modification *modification = add_single_modification(mod);
            flip_bits(modification->mods[0].value, mod->size);
            g_queue_push_tail(modifications, modification);
            break;
        }
        case 8: {
            uint64_t val;
            memcpy(&val, mod->value, 8);
            if (val != 0) {
                Modification *modification = add_single_modification(mod);
                memset(modification->mods[0].value, 0, 8);
                g_queue_push_tail(modifications, modification);
            }
            if (val != 1) {
                Modification *modification = add_single_modification(mod);
                uint64_t one = 1;
                memcpy(modification->mods[0].value, &one, 8);
                g_queue_push_tail(modifications, modification);
            }
            Modification *modification = add_single_modification(mod);
            flip_bits(modification->mods[0].value, mod->size);
            g_queue_push_tail(modifications, modification);
            break;
        }
        default: {
            // From real memcpy/memmove (if plt is given) or file write
            if (mod->size < 8) {
                flip_bits(mod->value, mod->size);
                Modification *modification = add_single_modification(mod);
                g_queue_push_tail(modifications, modification);
            } else {
                // TODO: fuzzing
            }
        }
    }
}

static void add_modification_pointer(GQueue *modifications, MutationCandidate *mod) {
    // For pointer, try null, valid
    target_ulong original;
    memcpy(&original, mod->value, sizeof(target_ulong));
    OspreyObject *obj = NULL;
    if (g_osprey_type_manager != NULL && mod->addr >= SNAPSHOT_PAGE_SIZE) {
        obj = osprey_object_get(g_osprey_type_manager, mod->addr, false);
    }
    // Null pointer -> valid pointer
    if (original == 0) {
        // Check if any valid pointer is available for the address
        if (obj != NULL) {
            if (obj->type && obj->type->kind == OSPREY_TYPE_POINTER) {
                OspreyType *pointee_type = obj->type->target;
                int type_size = osprey_type_size(pointee_type);
                // TODO: add to guest memory and get address
                trace_mem("[inferred] [pointee] [pointee-type %s] [addr %lx] [size %d]\n", pointee_type->id, mod->addr, type_size);
            }                
        }
    } else {
        // Valid pointer -> null pointer
        // TODO: Check if it can be null pointer
        memset(mod->value, 0, sizeof(target_ulong));
        Modification *modification = add_single_modification(mod);
        g_queue_push_tail(modifications, modification);
        // Valid pointer -> out-of-bounds pointer
        // TODO: Check if it can be out-of-bounds pointer (if it's pointer to the element of array)
        
    }
}

// static void clear_modification_queue(GQueue *queue) {
//     if (queue == NULL) {
//         return;
//     }
//     while (!g_queue_is_empty(queue)) {
//         Modification *mod = g_queue_pop_head(queue);
//         modification_free(mod);
//     }
// }

// static bool modification_equal(const Modification *lhs, const Modification *rhs) {
//     if (lhs == NULL || rhs == NULL) {
//         return false;
//     }
//     if (lhs->num_mods != rhs->num_mods) {
//         return false;
//     }
//     for (int i = 0; i < lhs->num_mods; i++) {
//         MutationCandidate *mod_lhs = &lhs->mods[i];
//         MutationCandidate *mod_rhs = &rhs->mods[i];
//         if (mod_lhs->addr != mod_rhs->addr || mod_lhs->size != mod_rhs->size) {
//             return false;
//         }
//         if (memcmp(mod_lhs->value, mod_rhs->value, mod_lhs->size) != 0) {
//             return false;
//         }
//     }
//     return true;
// }

// static bool modification_already_done(const ModificationManager *manager,
//                                       const Modification *candidate) {
//     if (manager == NULL || manager->done == NULL || manager->mod_maps == NULL || candidate == NULL || candidate->num_mods == 0) {
//         return false;
//     }

//     GArray *existing_mods = g_hash_table_lookup(manager->mod_maps, GUINT_TO_POINTER(candidate->mods[0].addr));
//     if (existing_mods != NULL) {
//         for (int i = 0; i < existing_mods->len; i++) {
//             Modification *existing_mod = g_array_index(existing_mods, Modification *, i);
//             if (modification_equal(candidate, existing_mod)) {
//                 return true;
//             }
//         }
//     }
//     return false;
// }

// static Expr* mutation_candidate_to_expr(const MutationCandidate *candidate) {
//     if (candidate == NULL) {
//         return NULL;
//     }

//     if (candidate->expr != NULL) {
//         return candidate->expr;
//     }

//     if (candidate->addr < SNAPSHOT_PAGE_SIZE) {
//         return candidate->expr;
//     }

//     return symbolic_rebuild_load_expr(candidate->addr, candidate->size,
//                                       candidate->value, 0);
// }

// TODO: call solver
static int snapshot_request_solver_modifications(GArray *primitive_candidates) {
    if (!binradar_solver_mutation_mode) {
        return -1;
    }
    if (shared_trace_data == NULL) {
        return -1;
    }
    return g_queue_get_length(mod_manager->modifications);
}

// In parent process, called after child execution
// Return: remaining modifications
static int analyze_collected_data(const ArgumentInfo *arg_info, size_t num_arg_regs) {
    if (shared_trace_data == NULL) {
        trace_mem("Snapshot init error: shared_trace_data is null\n");
        exit(1);
    }
    // Analyze exit reason
    SnapshotExitInfo *exit_info = snapshot_exit_info_ptr();
    if (!exit_info || !exit_info->valid) {
        trace_mem("[analyze] [exit-error] no exit info!!!\n");
        return 0;
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
    GArray *mod_primitive_candidates = g_array_new(FALSE, FALSE, sizeof(MutationCandidate));
    GArray *pointer_nodes = g_array_new(FALSE, FALSE, sizeof(PtrNode *));
    // First run: collect all data
    if (mod_manager == NULL) {
        mod_manager_init();
        
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
        // TODO: Add function argument (register) access
        for (size_t i = 0; i < num_arg_regs; i++) {
            if (arg_info[i].expr) {
                if (is_valid_address(arg_info[i].value, false)) {
                    // Treat as pointer access
                    trace_mem("[analyze] [sym-arg] [ptr] [reg %zu] [expr %lx]\n", i, arg_info[i].expr);
                } else {
                    // Treat as primitive access
                    MutationCandidate mc = {
                        .addr = (uintptr_t)arg_info[i].reg,
                        .size = sizeof(target_ulong),
                        .kind = 0,
                        .expr = arg_info[i].expr,
                        .value = {0}
                    };
                    memcpy(mc.value, &arg_info[i].value, sizeof(target_ulong));
                    g_array_append_val(mod_primitive_candidates, mc);
                    trace_mem("[analyze] [sym-arg] [prim] [reg %zu] [expr %lx]\n", i, arg_info[i].expr);
                }
            }
        }
        
        // Create modification list
        for (int i = 0; i < shared_trace_data->prim_idx; i++) {
            PrimitiveAccess *prim = &shared_trace_data->primitives[i];
            PrimitiveAccess *prim_data = g_new(PrimitiveAccess, 1);
            memcpy(prim_data, prim, sizeof(PrimitiveAccess));
            g_hash_table_insert(g_read_access_tainted_primitives_original, GUINT_TO_POINTER(prim_data->addr), prim_data);
            g_hash_table_insert(g_read_access_tainted_primitives_all, GUINT_TO_POINTER(prim_data->addr), prim_data);
            trace_mem("[analyze] [primitive] [index %d] [addr %lx] [size %d] [id %ld]\n", i, prim->addr, prim->size, prim->access_id);
            MutationCandidate mod = {
                .addr = prim->addr,
                .size = prim->size,
                .kind = 0,
                .expr = prim->expr,
                .value = {0}
            };
            // Get actual value
            if (prim->size <= 8) {
                void *ptr_h = g2h(prim->addr);
                memcpy(mod.value, ptr_h, prim->size);
            }
            // If type inference is available, apply type-specific modifications (e.g., for pointers, try null, valid, out-of-bounds)
            if (g_osprey_type_manager != NULL) {
                // Check if pointer
                OspreyObject *obj = osprey_object_get(g_osprey_type_manager, prim->addr, false);
                if (obj != NULL) {
                    if (obj->type) {
                        trace_mem("[memgraph] [prim] [type %s] [addr %lx]\n", obj->type->id, prim->addr);
                        if (obj->type->kind == OSPREY_TYPE_PRIMITIVE) {
                            // Primitive type: apply generic modifications
                            g_array_append_val(mod_primitive_candidates, mod);
                        } else if (obj->type->kind == OSPREY_TYPE_POINTER) {
                            // Build MemGraph (null pointer)
                            PtrNode *ptr_node = osprey_ptr_node_get(g_osprey_type_manager, prim->addr, false);
                            uint64_t target_value;
                            memcpy(&target_value, mod.value, sizeof(uint64_t));
                            if (ptr_node == NULL) {
                                ptr_node = osprey_ptr_node_get(g_osprey_type_manager, prim->addr, false);
                                if (ptr_node) {
                                    ptr_node->is_value_pointer = true;
                                    ptr_node->points_to = osprey_ptr_node_get(g_osprey_type_manager, target_value, true);
                                    osprey_ptr_edge_create(g_osprey_type_manager, ptr_node, ptr_node->points_to);
                                    g_array_append_val(pointer_nodes, ptr_node);
                                } else {
                                    trace_mem("[memgraph] [pointer-error] [no-node] [addr %lx]\n", prim->addr);
                                }
                            }
                        }
                    } else {
                        // Non-pointer type: apply generic modifications
                        g_array_append_val(mod_primitive_candidates, mod);
                    }
                } else {
                    // No type information: assume as primitive type
                    g_array_append_val(mod_primitive_candidates, mod);
                }
                continue;
            } else {
                // No type inference: apply generic modifications
                add_modification_primitive(mod_manager->modifications, &mod);
            }
        }
        for (int i = 0; i < shared_trace_data->ptr_idx; i++) {
            PointerAccess *ptr = &shared_trace_data->pointers[i];
            PointerAccess *ptr_data = g_new(PointerAccess, 1);
            memcpy(ptr_data, ptr, sizeof(PointerAccess));
            g_hash_table_insert(g_read_access_pointers_original, GUINT_TO_POINTER(ptr_data->addr), ptr_data);
            g_hash_table_insert(g_read_access_pointers_all, GUINT_TO_POINTER(ptr_data->addr), ptr_data);
            trace_mem("[analyze] [pointer] [index %d] [addr %lx] [target %lx] [id %ld]\n", i, ptr->addr, ptr->target, ptr->access_id);
            MutationCandidate mod = {
                .addr = ptr->addr,
                .size = sizeof(target_ulong),
                .kind = 1,
                .expr = ptr->expr,
                .value = {0}
            };
            // Get actual value
            target_ulong actual_value;
            memcpy(&actual_value, g2h(ptr->addr), sizeof(target_ulong));
            memcpy(mod.value, &actual_value, sizeof(target_ulong));
            // Check type inference
            if (g_osprey_type_manager != NULL) {
                OspreyObject *obj = osprey_object_get(g_osprey_type_manager, ptr->addr, false);
                if (obj != NULL) {
                    trace_mem("[memgraph] [pointer] [type %s] [addr %lx] [target %lx]\n", obj->type ? obj->type->id : "unknown", ptr->addr, ptr->target);
                    // add_modification_pointer(mod_manager->modifications, &mod);
                    PtrNode *ptr_node = osprey_ptr_node_get(g_osprey_type_manager, ptr->addr, false);
                    if (ptr_node) {
                        ptr_node->is_value_pointer = true;
                        ptr_node->points_to = osprey_ptr_node_get(g_osprey_type_manager, ptr->target, true);
                        osprey_ptr_edge_create(g_osprey_type_manager, ptr_node, ptr_node->points_to);
                        g_array_append_val(pointer_nodes, ptr_node);
                    } else {
                        trace_mem("[memgraph] [pointer-error] [no-node] [addr %lx]\n", ptr->addr);
                    }
                }
                continue;
            } else {
                add_modification_pointer(mod_manager->modifications, &mod);
            }
        }

        // Use MemGraph to find candidate modifications
        if (g_osprey_type_manager != NULL) {
            GHashTable *visited_obj_nodes = g_hash_table_new(g_direct_hash,
                                                             g_direct_equal);
            GHashTable *terminal_obj_set = g_hash_table_new(g_direct_hash,
                                                            g_direct_equal);
            GHashTable *terminal_pointing_set = g_hash_table_new(g_direct_hash,
                                                                  g_direct_equal);
            GArray *terminal_nodes = g_array_new(FALSE, FALSE, sizeof(ObjNode *));
            GArray *terminal_pointing_nodes = g_array_new(FALSE, FALSE,
                                                          sizeof(PtrNode *));
            GQueue *pending_obj_nodes = g_queue_new();

            for (int i = pointer_nodes->len - 1; i >= 0; i--) {
                PtrNode *ptr_node = g_array_index(pointer_nodes, PtrNode *, i);
                if (ptr_node == NULL || ptr_node->base == NULL) {
                    continue;
                }
                if (g_hash_table_contains(visited_obj_nodes, ptr_node->base)) {
                    continue;
                }

                g_queue_push_tail(pending_obj_nodes, ptr_node->base);
                while (!g_queue_is_empty(pending_obj_nodes)) {
                    ObjNode *obj_node = (ObjNode *)g_queue_pop_head(
                        pending_obj_nodes);
                    if (obj_node == NULL) {
                        continue;
                    }
                    if (g_hash_table_contains(visited_obj_nodes, obj_node)) {
                        continue;
                    }
                    g_hash_table_add(visited_obj_nodes, obj_node);

                    bool has_unvisited_pointer_edge = false;
                    for (guint j = 0; j < obj_node->outgoing_ptr_edges->len; j++) {
                        PtrEdge *edge = g_array_index(obj_node->outgoing_ptr_edges,
                                                      PtrEdge *, j);
                        if (edge == NULL || edge->dst == NULL) {
                            continue;
                        }
                        if (!edge->dst->is_value_pointer || edge->dst->base == NULL) {
                            continue;
                        }
                        if (!g_hash_table_contains(visited_obj_nodes,
                                                   edge->dst->base)) {
                            has_unvisited_pointer_edge = true;
                            g_queue_push_tail(pending_obj_nodes,
                                              edge->dst->base);
                        }
                    }

                    if (!has_unvisited_pointer_edge) {
                        if (!g_hash_table_contains(terminal_obj_set, obj_node)) {
                            g_hash_table_add(terminal_obj_set, obj_node);
                            g_array_append_val(terminal_nodes, obj_node);
                        }
                    }
                }
            }

            for (int i = 0; i < pointer_nodes->len; i++) {
                PtrNode *src_node = g_array_index(pointer_nodes, PtrNode *, i);
                if (src_node == NULL || src_node->base == NULL) {
                    continue;
                }
                ObjNode *base = src_node->base;
                for (guint j = 0; j < base->outgoing_ptr_edges->len; j++) {
                    PtrEdge *edge = g_array_index(base->outgoing_ptr_edges,
                                                  PtrEdge *, j);
                    if (edge == NULL || edge->dst == NULL || edge->dst->base == NULL) {
                        continue;
                    }
                    if (!g_hash_table_contains(terminal_obj_set, edge->dst->base)) {
                        continue;
                    }
                    if (!g_hash_table_contains(terminal_pointing_set, src_node)) {
                        g_hash_table_add(terminal_pointing_set, src_node);
                        g_array_append_val(terminal_pointing_nodes, src_node);
                    }
                }
            }

            trace_mem("[memgraph] [candidate] [terminal %d] [pointing %d]\n",
                      terminal_nodes->len, terminal_pointing_nodes->len);
            // Generate modifications using solver
            snapshot_request_solver_modifications(mod_primitive_candidates);

            g_queue_free(pending_obj_nodes);
            g_array_free(terminal_nodes, TRUE);
            g_array_free(terminal_pointing_nodes, TRUE);
            g_hash_table_destroy(visited_obj_nodes);
            g_hash_table_destroy(terminal_obj_set);
            g_hash_table_destroy(terminal_pointing_set);
        }
        trace_mem("[analyze] [queue] [len %d]\n", g_queue_get_length(mod_manager->modifications));
    } else {
        // TODO: Implement feedback loop
        // // Collect only delta, give feedback
        // if (original_exit_info.crashed && exit_info->crashed) {
            
        // } else if (original_exit_info.crashed && !exit_info->crashed) {
            
        // }
        // // Append modification list
        // for (int i = 0; i < shared_trace_data->prim_idx; i++) {
        //     PrimitiveAccess *prim = &shared_trace_data->primitives[i];
        //     if (!g_hash_table_lookup(g_read_access_tainted_primitives_original, GUINT_TO_POINTER(prim->addr))) {
        //         // TODO: New value
        //     }
        //     if (!g_hash_table_lookup(g_read_access_tainted_primitives_all, GUINT_TO_POINTER(prim->addr))) {
        //         // Found new read
        //         PrimitiveAccess *prim_data = g_new(PrimitiveAccess, 1);
        //         memcpy(prim_data, prim, sizeof(PrimitiveAccess));
        //         g_hash_table_insert(g_read_access_tainted_primitives_all, GUINT_TO_POINTER(prim_data->addr), prim_data);
        //         trace_mem("[analyze] [new-primitive] [index %d] [addr %lx] [size %d] [id %ld]\n", i, prim->addr, prim->size, prim->access_id);
        //         MutationCandidate mod = {
        //             .addr = prim->addr,
        //             .size = prim->size,
        //             .value = {0}
        //         };
        //         // Get actual value
        //         if (prim->size <= 8) {
        //             void *ptr_h = g2h(prim->addr);
        //             memcpy(mod.value, ptr_h, prim->size);
        //         }
        //         // If type inference is available, apply type-specific modifications (e.g., for pointers, try null, valid, out-of-bounds)
        //         if (g_osprey_type_manager != NULL) {
        //             // Check if pointer
        //             OspreyObject *obj = osprey_object_get(g_osprey_type_manager,
        //                                                     prim->addr, false);
        //             if (obj->type && obj->type->kind == OSPREY_TYPE_POINTER) {
        //                 add_modification_pointer(mod_manager->modifications, &mod);
        //             }
        //         } else {
        //             // No type inference: apply generic modifications
        //             add_modification_primitive(mod_manager->modifications, &mod);
        //         }
        //     }
        // }
        // for (int i = 0; i < shared_trace_data->ptr_idx; i++) {
        //     PointerAccess *ptr = &shared_trace_data->pointers[i];
        //     if (!g_hash_table_lookup(g_read_access_pointers_original, GUINT_TO_POINTER(ptr->addr))) {
        //         // New pointer read
        //     }
        //     if (!g_hash_table_lookup(g_read_access_pointers_all, GUINT_TO_POINTER(ptr->addr))) {
        //         // Found new read
        //         PointerAccess *ptr_data = g_new(PointerAccess, 1);
        //         memcpy(ptr_data, ptr, sizeof(PointerAccess));
        //         g_hash_table_insert(g_read_access_pointers_all, GUINT_TO_POINTER(ptr_data->addr), ptr_data);
        //         trace_mem("[analyze] [new-pointer] [index %d] [addr %lx] [target %lx] [id %ld]\n", i, ptr->addr, ptr->target, ptr->access_id);
        //         MutationCandidate mod = {
        //             .addr = ptr->addr,
        //             .size = sizeof(target_ulong),
        //             .value = {0}
        //         };
        //         // Get actual value
        //         target_ulong actual_value;
        //         memcpy(&actual_value, g2h(ptr->addr), sizeof(target_ulong));
        //         memcpy(mod.value, &actual_value, sizeof(target_ulong));
        //         add_modification_pointer(mod_manager->modifications, &mod);
        //     }
        // }
    }
    g_array_free(pointer_nodes, true);
    g_array_free(mod_primitive_candidates, true);
    // Select one modification
    g_array_append_val(mod_manager->done, mod_manager->current);
    mod_manager->current = g_queue_pop_head(mod_manager->modifications);
    // TODO: restore file offset if needed
    if (mod_manager->current == NULL) {
        trace_mem("[analyze] [done] consumed all modifications\n");
        return 0;
    }
    // Clean expr and query added during child execution
    if (!binradar_preserve_child_queries) {
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
    }
    // Finished: reset shared_trace_data
    memset(shared_trace_data, 0, sizeof(SharedTraceData));
    return g_queue_get_length(mod_manager->modifications);
}

void snapshot_forkserver(CPUState *cpu, CPUArchState *cpu_env, const ArgumentInfo *arg_info, size_t num_arg_regs) {
    trace_mem("[snapshot] [forkserver] [called %d]\n", forkserver_installed);
    fflush(stderr);
    if (forkserver_installed) return;
    forkserver_installed = true;
    rcu_disable_atfork();
    snapshot_save();
    pid_t child_pid;
    // int   t_fd[2];
    
    uint32_t   was_killed;
    uint32_t version = 0x41464c00;
    uint32_t tmp = version ^ 0xffffffff, status2, status = version;
    uint8_t *msg = (uint8_t *)&status;
    uint8_t *reply = (uint8_t *)&status2;
    uint32_t analyze_result_len = 0;
    uint32_t analyze_result_len_prev = 0;
    uint8_t *analyze_result = NULL;
  
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
            trace_mem("[forkserver] [exit] parent (fuzzolic) dead or exit\n");
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
            snapshot_modify_memory(cpu_env);
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

        // Child process exit
        if (write(FORKSRV_FD + 1, &status, 4) != 4) exit(7);

        // Get type inference result
        if (read(FORKSRV_FD, &analyze_result_len, 4) != 4) {
            trace_mem("[forkserver] [error] failed to read analyze_result_len from %d\n", FORKSRV_FD);
            exit(8);
        }
        trace_mem("[forkserver] [analyze-result] [len %lu]\n", analyze_result_len);

        if (analyze_result_len > 0) {
            if (analyze_result_len > analyze_result_len_prev) {
                g_free(analyze_result);
                analyze_result = g_malloc(analyze_result_len + 1);
                analyze_result_len_prev = analyze_result_len;
            }
            size_t total_read = 0;
            while (total_read < analyze_result_len) {
                ssize_t bytes_read = read(FORKSRV_FD, analyze_result + total_read, analyze_result_len - total_read);
                if (bytes_read <= 0) {
                    trace_mem("[forkserver] [error] failed to read analyze_result from %d\n", FORKSRV_FD);
                    exit(9);
                }
                total_read += bytes_read;
            }
            analyze_result[analyze_result_len] = '\0';
            trace_mem("[forkserver] [analyze-result] [accept %lu]\n", analyze_result_len);
            snapshot_load_inferred_types(analyze_result);
        }

        int remaining = analyze_collected_data(arg_info, num_arg_regs);
        
        // Send remaining count
        if (write(FORKSRV_FD + 1, &remaining, 4) != 4) exit(10);
  
    }

}

static sbsv_status custom_hex(const char* input, sbsv_value* out_value, void* user_data) {
    char* end_ptr;
    (void)user_data;
    out_value->type = SBSV_VALUE_INT;
    out_value->data.int_value = strtoll(input, &end_ptr, 16);
    if (*end_ptr != '\0') {
        return SBSV_ERR_INVALID_ARG;
    }
    return SBSV_OK;
}

static sbsv_status custom_region_type(const char* input, sbsv_value* out_value, void* user_data) {
    (void)user_data;
    out_value->type = SBSV_VALUE_INT;
    if (strcmp(input, "S") == 0) {
        out_value->data.int_value = 0;
    } else if (strcmp(input, "H") == 0) {
        out_value->data.int_value = 1;
    } else if (strcmp(input, "G") == 0) {
        out_value->data.int_value = 2;
    } else {
        return SBSV_ERR_INVALID_ARG;
    }
    return SBSV_OK;
}

static void osprey_type_manager_add_type(OspreyTypeManager *manager, OspreyType *type) {
    g_hash_table_insert(manager->type_table, type->id, type);
}

static void osprey_type_manager_add_addr_to_type_id(OspreyTypeManager *manager, uint64_t addr, OspreyType *type) {
    g_hash_table_insert(manager->addr_to_type_id,
                        GSIZE_TO_POINTER((gsize)addr), g_strdup(type->id));
}

static void osprey_type_parse_field(OspreyType *type, int64_t base_offset, const char *id, const sbsv_value_list *field_list) {
    type->kind = OSPREY_TYPE_STRUCT;
    type->id = g_strdup(id);
    type->meta.struct_info.fields = g_array_new(false, false, sizeof(OspreyStructField));
    int64_t max_offset = 0;
    for (int i = 0; i < field_list->count; i++) {
        char type_id[256];
        int64_t offset, size;
        if (sscanf(field_list->items[i].data.string_value, "%lx(%lxB):%256[^,]", &offset, &size, type_id) == 3) {
            OspreyStructField field = {
                .offset = offset,
                .size = size,
                .type_id = g_strdup(type_id)
            };
            g_array_append_val(type->meta.struct_info.fields, field);
            if (offset + size > max_offset) {
                max_offset = offset + size;
            }
        }
    }
    // type->meta.struct_info.total_size = max_offset - base_offset;
}

void snapshot_load_inferred_types(uint8_t *analyze_result) {
    if (g_osprey_type_manager == NULL) {
        g_osprey_type_manager = osprey_type_manager_new();
    }
    sbsv_parser *parser = sbsv_parser_new(SBSV_PARSER_DEFAULT);
    sbsv_parser_add_custom_type(parser, "hex", custom_hex, NULL);
    sbsv_parser_add_custom_type(parser, "region_type", custom_region_type, NULL);
    sbsv_parser_add_schema(parser, "[type-def] [primitive] [id: str] [size: int] [body: str]");
    sbsv_parser_add_schema(parser, "[type-def] [array] [id: str] [RT: region_type] [RB: hex] [RI: hex] [lo: hex] [hi: hex] [elem-type: str] [count: int]");
    sbsv_parser_add_schema(parser, "[type-def] [struct] [id: str] [RT: region_type] [RB: hex] [RI: hex] [base: hex] [fields: list[str]]");
    sbsv_parser_add_schema(parser, "[type-def] [pointer] [id: str] [to-val: str] [to-role: str]");
    sbsv_parser_add_schema(parser, "[struct-base] [base: hex] [offset: hex] [type: str]");
    sbsv_parser_add_schema(parser, "[field] [RT: region_type] [RB: hex] [RI: hex] [off: hex] [sz: hex] [base: hex] [type: str] [P: float]");
    sbsv_parser_add_schema(parser, "[array-start] [RT: region_type] [RB: hex] [RI: hex] [type: str] [lo: hex] [hi: hex] [elem: str] [P: float]");
    sbsv_parser_add_schema(parser, "[array-elem] [RT: region_type] [RB: hex] [RI: hex] [off: hex] [sz: hex] [type: str] [array-offset: hex] [array-id: str] [idx: int] [P: float]");
    sbsv_parser_add_schema(parser, "[scalar] [RT: region_type] [RB: hex] [RI: hex] [off: hex] [sz: hex] [type: str] [P: float]");
    sbsv_parser_add_schema(parser, "[pointer-var] [RT: region_type] [RB: hex] [RI: hex] [off: hex] [sz: hex] [type: str] [target: hex] [t-role: str] [t-val: str] [P: float]");
    // trace_mem("%s", (const char *)analyze_result);
    if (sbsv_parser_loads(parser, (const char *)analyze_result) != SBSV_OK) {
        trace_mem("Failed to load inferred types - %s\n", sbsv_parser_last_error(parser));
        sbsv_parser_free(parser);
        return;
    }
    trace_mem("[snapshot] [load-inferred-types] [start]\n");
    const sbsv_row** rows = NULL;
    size_t num_rows = 0;
    int valid = 1;
    GArray *primitive_types = g_array_new(false, false, sizeof(OspreyType *));
    // 1. Load type definitions
    sbsv_parser_get_rows(parser, "[type-def] [primitive]", &rows, &num_rows);
    for (size_t i = 0; i < num_rows; i++) {
        const sbsv_row *r = rows[i];
        const char *id = sbsv_row_get_string(r, "id");
        long long size = sbsv_row_get_int(r, "size", &valid);
        // const char *body = sbsv_row_get_string(r, "body");
        OspreyType *type = g_new0(OspreyType, 1);
        type->kind = OSPREY_TYPE_PRIMITIVE;
        type->id = g_strdup(id);
        type->size = size;
        type->is_pointer = false;
        osprey_type_manager_add_type(g_osprey_type_manager, type);
        g_array_append_val(primitive_types, type);
        // trace_mem("[inferred-type] [primitive] [id %s] [size %lld] [body %s]\n", id, size, body);
    }
    sbsv_free_row_ref_array(rows);

    sbsv_parser_get_rows(parser, "[type-def] [array]", &rows, &num_rows);
    for (size_t i = 0; i < num_rows; i++) {
        const sbsv_row *r = rows[i];
        const char *id = sbsv_row_get_string(r, "id");
        // int region_type = sbsv_row_get_int(r, "RT", &valid);
        // uint64_t region_base = sbsv_row_get_int(r, "RB", &valid);
        // uint64_t region_size = sbsv_row_get_int(r, "RI", &valid);
        // int64_t lo = sbsv_row_get_int(r, "lo", &valid);
        // int64_t hi = sbsv_row_get_int(r, "hi", &valid);
        const char *elem_type = sbsv_row_get_string(r, "elem-type");
        int64_t count = sbsv_row_get_int(r, "count", &valid);
        OspreyType *type = g_new0(OspreyType, 1);
        type->kind = OSPREY_TYPE_ARRAY;
        type->id = g_strdup(id);
        type->target_type_id = g_strdup(elem_type);
        type->meta.array_info.count = count;
        osprey_type_manager_add_type(g_osprey_type_manager, type);
    }
    sbsv_free_row_ref_array(rows);

    sbsv_parser_get_rows(parser, "[type-def] [struct]", &rows, &num_rows);
    for (size_t i = 0; i < num_rows; i++) {
        const sbsv_row *r = rows[i];
        const char *id = sbsv_row_get_string(r, "id");
        // int region_type = sbsv_row_get_int(r, "RT", &valid);
        int64_t region_base = sbsv_row_get_int(r, "RB", &valid);
        // int64_t region_size = sbsv_row_get_int(r, "RI", &valid);
        int64_t base_offset = sbsv_row_get_int(r, "base", &valid);
        const sbsv_value_list *fields = sbsv_row_get_list(r, "fields");
        OspreyType *type = g_new0(OspreyType, 1);
        osprey_type_parse_field(type, base_offset, id, fields);
        osprey_type_manager_add_type(g_osprey_type_manager, type);
        osprey_type_manager_add_addr_to_type_id(g_osprey_type_manager, (uint64_t)(region_base + base_offset), type);
    }
    sbsv_free_row_ref_array(rows);

    sbsv_parser_get_rows(parser, "[type-def] [pointer]", &rows, &num_rows);
    for (size_t i = 0; i < num_rows; i++) {
        const sbsv_row *r = rows[i];
        const char *id = sbsv_row_get_string(r, "id");
        const char *to = sbsv_row_get_string(r, "to-val");
        const char *to_role = sbsv_row_get_string(r, "to-role");
        OspreyType *type = g_new0(OspreyType, 1);
        type->kind = OSPREY_TYPE_POINTER;
        type->id = g_strdup(id);
        type->target_type_id = g_strdup(to);
        type->meta.pointer_info.target_role = g_strdup(to_role);
        osprey_type_manager_add_type(g_osprey_type_manager, type);
    }
    sbsv_free_row_ref_array(rows);

    // 2. Match inferred types with actual addresses
    // 2.1: MemoryAddress -> Type ID (array_start, struct)
    sbsv_parser_get_rows(parser, "[array-start]", &rows, &num_rows);
    for (size_t i = 0; i < num_rows; i++) {
        const sbsv_row *r = rows[i];
        // int region_type = sbsv_row_get_int(r, "RT", &valid);
        int64_t region_base = sbsv_row_get_int(r, "RB", &valid);
        // int64_t region_size = sbsv_row_get_int(r, "RI", &valid);
        const char *type_id = sbsv_row_get_string(r, "type");
        int64_t lo = sbsv_row_get_int(r, "lo", &valid);
        int64_t hi = sbsv_row_get_int(r, "hi", &valid);
        // const char *elem = sbsv_row_get_string(r, "elem");
        // double p = sbsv_row_get_float(r, "P", &valid);
        OspreyObject *obj = osprey_address_get(g_osprey_type_manager, region_base + lo, true);
        obj->role = OSPREY_ROLE_ARRAY_START;
        obj->size = hi - lo;
        obj->type = osprey_type_get(g_osprey_type_manager, type_id);
        if (obj->type == NULL) {
            trace_mem("Failed to find type for array start: %s\n", type_id);
        }
        ObjNode *obj_node = osprey_obj_node_get(g_osprey_type_manager, region_base + lo, true);
        obj_node->obj = obj;
    }
    sbsv_free_row_ref_array(rows);

    sbsv_parser_get_rows(parser, "[struct-base]", &rows, &num_rows);
    for (size_t i = 0; i < num_rows; i++) {
        const sbsv_row *r = rows[i];
        int64_t base = sbsv_row_get_int(r, "base", &valid);
        const char *type_id = sbsv_row_get_string(r, "type");
        OspreyObject *obj = osprey_address_get(g_osprey_type_manager, base, true);
        obj->role = OSPREY_ROLE_STRUCT_BASE;
        obj->type = osprey_type_get(g_osprey_type_manager, type_id);
        if (obj->type == NULL) {
            trace_mem("Failed to find type for struct base: %s\n", type_id);
        }
        ObjNode *obj_node = osprey_obj_node_get(g_osprey_type_manager, base, true);
        obj_node->obj = obj;
    }
    sbsv_free_row_ref_array(rows);

    // 2.2: MemoryChunk -> Type ID (scalar, pointer, array_elem, field)
    sbsv_parser_get_rows(parser, "[scalar]", &rows, &num_rows);
    for (size_t i = 0; i < num_rows; i++) {
        const sbsv_row *r = rows[i];
        // int region_type = sbsv_row_get_int(r, "RT", &valid);
        int64_t region_base = sbsv_row_get_int(r, "RB", &valid);
        // int64_t region_size = sbsv_row_get_int(r, "RI", &valid);
        int64_t off = sbsv_row_get_int(r, "off", &valid);
        int64_t sz = sbsv_row_get_int(r, "sz", &valid);
        // double p = sbsv_row_get_float(r, "P", &valid);
        OspreyObject *obj = osprey_object_get(g_osprey_type_manager, region_base + off, true);
        obj->role = OSPREY_ROLE_SCALAR;
        // obj->type_id = g_strdup()
        for (size_t j = 0; j < primitive_types->len; j++) {
            OspreyType *type = g_array_index(primitive_types, OspreyType *, j);
            if (type->size == sz) {
                obj->type = type;
                break;
            }
        }
    }
    sbsv_free_row_ref_array(rows);

    sbsv_parser_get_rows(parser, "[pointer-var]", &rows, &num_rows);
    for (size_t i = 0; i < num_rows; i++) {
        const sbsv_row *r = rows[i];
        // int region_type = sbsv_row_get_int(r, "RT", &valid);
        int64_t region_base = sbsv_row_get_int(r, "RB", &valid);
        // int64_t region_size = sbsv_row_get_int(r, "RI", &valid);
        int64_t off = sbsv_row_get_int(r, "off", &valid);
        int64_t size = sbsv_row_get_int(r, "sz", &valid);
        // int64_t target = sbsv_row_get_int(r, "target", &valid);
        const char *type_id = sbsv_row_get_string(r, "type");
        // const char *t_val = sbsv_row_get_string(r, "t-val");
        // double p = sbsv_row_get_float(r, "P", &valid);
        // trace_mem("[inferred-type] [pointer] [region-type %d] [region-base %lx] [region-size %lx] [off %lx] [size %lx] [target %lx] [type-id %s] [P %f]\n", region_type, region_base, region_size, off, size, target, type_id, p);
        OspreyObject *obj = osprey_object_get(g_osprey_type_manager, region_base + off, true);
        obj->role = OSPREY_ROLE_SCALAR;
        obj->size = size;
        obj->type = osprey_type_get(g_osprey_type_manager, type_id);
        PtrNode *ptr_node = osprey_ptr_node_get(g_osprey_type_manager, region_base + off, true);
        ptr_node->is_value_pointer = true;
    }
    sbsv_free_row_ref_array(rows);

    sbsv_parser_get_rows(parser, "[array-elem]", &rows, &num_rows);
    for (size_t i = 0; i < num_rows; i++) {
        const sbsv_row *r = rows[i];
        // int region_type = sbsv_row_get_int(r, "RT", &valid);
        int64_t region_base = sbsv_row_get_int(r, "RB", &valid);
        // int64_t region_size = sbsv_row_get_int(r, "RI", &valid);
        int64_t off = sbsv_row_get_int(r, "off", &valid);
        int64_t sz = sbsv_row_get_int(r, "sz", &valid);
        int64_t array_start_offset = sbsv_row_get_int(r, "array-offset", &valid);
        const char *type_id = sbsv_row_get_string(r, "type");
        // double p = sbsv_row_get_float(r, "P", &valid);
        OspreyObject *obj = osprey_object_get(g_osprey_type_manager, region_base + off, true);
        obj->role = OSPREY_ROLE_ARRAY_ELEM;
        obj->size = sz;
        obj->type = osprey_type_get(g_osprey_type_manager, type_id);
        int64_t array_start_addr = region_base + array_start_offset;
        OspreyObject *array_start_obj = osprey_address_get(g_osprey_type_manager, array_start_addr, false);
        obj->parent = array_start_obj;
        ObjNode *obj_node = osprey_obj_node_get(g_osprey_type_manager, region_base + off, false);
        if (obj_node == NULL) {
            obj_node = osprey_obj_node_get(g_osprey_type_manager, region_base + off, true);
        }
        if (obj_node != NULL && obj_node->obj == NULL) {
            obj_node->obj = obj;
        }
        if (obj->type != NULL && obj->type->kind == OSPREY_TYPE_POINTER) {
            PtrNode *ptr_node = osprey_ptr_node_get(g_osprey_type_manager, region_base + off, true);
            ptr_node->is_value_pointer = true;
            ptr_node->base = osprey_obj_node_get(g_osprey_type_manager, array_start_addr, false);
        } else if (obj->type == NULL) {
            trace_mem("[inferred-type] [array-elem] missing type [addr %lx] [type-id %s]\n",
                      (uint64_t)(region_base + off), type_id ? type_id : "(null)");
        }
    }
    sbsv_free_row_ref_array(rows);

    sbsv_parser_get_rows(parser, "[field]", &rows, &num_rows);
    for (size_t i = 0; i < num_rows; i++) {
        const sbsv_row *r = rows[i];
        // int region_type = sbsv_row_get_int(r, "RT", &valid);
        int64_t region_base = sbsv_row_get_int(r, "RB", &valid);
        // int64_t region_size = sbsv_row_get_int(r, "RI", &valid);
        int64_t off = sbsv_row_get_int(r, "off", &valid);
        int64_t sz = sbsv_row_get_int(r, "sz", &valid);
        int64_t base = sbsv_row_get_int(r, "base", &valid);
        const char *type_id = sbsv_row_get_string(r, "type");
        // double p = sbsv_row_get_float(r, "P", &valid);
        OspreyObject *obj = osprey_object_get(g_osprey_type_manager, region_base + off, true);
        obj->role = OSPREY_ROLE_FIELD;
        obj->size = sz;
        obj->type = osprey_type_get(g_osprey_type_manager, type_id);
        OspreyObject *base_obj = osprey_address_get(g_osprey_type_manager, region_base + base, false);
        
        if (obj->type != NULL && obj->type->kind == OSPREY_TYPE_POINTER) {
            PtrNode *ptr_node = osprey_ptr_node_get(g_osprey_type_manager, region_base + off, true);
            ptr_node->is_value_pointer = true;
            ptr_node->base = osprey_obj_node_get(g_osprey_type_manager, region_base + base, false);
        } else if (obj->type == NULL) {
            trace_mem("[inferred-type] [field] missing type [addr %lx] [type-id %s]\n",
                      (uint64_t)(region_base + off), type_id ? type_id : "(null)");
        }
        
        if (base_obj != NULL) {
            obj->parent = base_obj;
        }
        if (obj->type == NULL) {
            // Primitive type
            for (size_t j = 0; j < primitive_types->len; j++) {
                OspreyType *type = g_array_index(primitive_types, OspreyType *, j);
                if (type->size == sz) {
                    obj->type = type;
                    break;
                }
            }
        }
    }
    sbsv_free_row_ref_array(rows);

    // Finished loading, free parser
    sbsv_parser_free(parser);

    // 3. Resolve type references
    GHashTableIter iter;
    gpointer key, value;
    g_hash_table_iter_init(&iter, g_osprey_type_manager->type_table);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        OspreyType *type = (OspreyType *)value;
        switch (type->kind) {
            case OSPREY_TYPE_PRIMITIVE:
                type->is_pointer = false;
                break;
            case OSPREY_TYPE_POINTER:
                type->is_pointer = true;
                type->size = sizeof(target_ulong);
                type->target = osprey_type_get(g_osprey_type_manager, type->target_type_id);
                break;
            case OSPREY_TYPE_ARRAY:
                type->is_pointer = false;
                type->target = osprey_type_get(g_osprey_type_manager, type->target_type_id);
                break;
            case OSPREY_TYPE_STRUCT:
                type->is_pointer = false;
                for (size_t i = 0; i < type->meta.struct_info.fields->len; i++) {
                    OspreyStructField *field = &g_array_index(type->meta.struct_info.fields, OspreyStructField, i);
                    field->type = osprey_type_get(g_osprey_type_manager, field->type_id);
                }
                break;
        }
    }
    g_hash_table_iter_init(&iter, g_osprey_type_manager->addr_to_type);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        // uint64_t addr = GPOINTER_TO_UINT(key);
        OspreyObject *obj = (OspreyObject *)value;
        if (obj->type == NULL) {
            trace_mem("Failed to find type for address %lx, role %d\n", obj->addr, obj->role);
        }
    }
    g_hash_table_iter_init(&iter, g_osprey_type_manager->obj_addr_to_type);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        // uint64_t addr = GPOINTER_TO_UINT(key);
        OspreyObject *obj = (OspreyObject *)value;
        if (obj->type == NULL) {
            trace_mem("Failed to find type for object address %lx, role %d\n", obj->addr, obj->role);
        }
    }
    trace_mem("[snapshot] [load-inferred-types] [finish]\n");
}