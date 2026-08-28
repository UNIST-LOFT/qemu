#include "snapshot.h"
#include "provenance.h"
#include "sem-events.h"
#include "osprey.h"
#include "osprey-internal.h"
#include "../tcg/symbolic/symbolic-struct.h"
#include "sbsv.h"
#include "qemu/rcu.h"

#include <fcntl.h>
#include <poll.h>
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

/* Phase 4: exact syscall output sizes.  Verify the target ABI struct
 * sizes at compile time so snapshot_syscall() can invalidate exactly the
 * bytes the kernel wrote, replacing the old conservative 256-byte windows. */
_Static_assert(sizeof(struct target_stat) == 144, "x86_64 target_stat ABI size");
_Static_assert(sizeof(struct target_statfs) == 120, "x86_64 target_statfs ABI size");
_Static_assert(sizeof(struct target_statx) == 256, "x86_64 target_statx ABI size");

extern target_ulong target_brk;
bool restoring_to_snapshot;
target_ulong binradar_entrypoint = (target_ulong)-1;

extern Query *query_queue;
extern Query *next_query;
extern uint64_t symbolic_start_code;
extern uint64_t symbolic_end_code;

static uint64_t binradar_entrypoint_hit_count   = 0;
static uint64_t binradar_forkserver_target_hit_count = 1;
static int      binradar_forkserver_enable      = -1;
static int      binradar_preserve_child_queries = -1;
static int      binradar_solver_mutation_mode   = -1;
static int      binradar_forkserver_ctrl_r = -1;
static int      binradar_forkserver_stat_w = -1;
static char*    binradar_probe_file     = NULL;
static char*    binradar_query_window_file = NULL;
static uint8_t  binradar_query_window_dumped    = 0;

bool forkserver_installed = false;
unsigned char afl_fork_child;
unsigned int  afl_forksrv_pid;
typedef struct exclude_region {
    uintptr_t start;
    uintptr_t end;
} exclude_region;

exclude_region binradar_exclude_regions[4] = {
    {0, 0}, // PATCH_RESERVE_RANGE
    {0, 0}, // E9_TRAMPOLINE_RANGE
    {0, 0}, // E9_LOADER_RANGE
    {0, 0}
};

typedef struct e9_relocated_call {
    target_ulong jump_addr;
    target_ulong call_site;
    target_ulong ret_addr;
} e9_relocated_call;

static e9_relocated_call *e9_relocated_calls = NULL;
static size_t e9_relocated_calls_len = 0;
static size_t e9_relocated_calls_cap = 0;

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

typedef struct DynStackFrame {
    uint64_t frame_id;
    target_ulong entry_sp;
    target_ulong min_sp;
    target_ulong call_pc;
    target_ulong ret_pc;
    target_ulong maybe_rbp;
    bool has_rbp;
    bool imprecise;
    bool synthetic;
    SnapshotMemRegion region;
} DynStackFrame;

static uint64_t next_dyn_frame_id = 1;

static SnapshotMemRegionManager mr_manager;
static GArray *pending_allocs = NULL;

/* ---- QASAN-like concrete bounds checking ---- */
int binradar_memcheck_enabled = 0;
#define HEAP_QUARANTINE_MAX_BYTES (50 * 1024 * 1024)
static GQueue *heap_quarantine = NULL;
static size_t heap_quarantine_bytes = 0;

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
    /* Deferred provenance finding.  Lives in the shared mmap so the
     * parent can read it after waitpid even when the child was killed or
     * timed out (timeout-safe transport; see Step 5). */
    PendingProvenanceFault prov_pending_fault;
    PrimitiveAccess primitives[MAX_PRIMITIVE_ACCESS];
    PointerAccess pointers[MAX_POINTER_ACCESS];
} SharedTraceData;


typedef struct PatchedResult {
    uint32_t patch_id;
    GArray *br_taken; // Array<int> (0 = not taken, 1 = taken, 2 = patch crashed)
    bool is_crash;
    uint64_t fault_loc;
} PatchedResult;

typedef struct BinradarResult {
    uint32_t iter;
    PatchedResult *patch_results; // Array<PatchedResult *>, length = patch_cnt + 1
} BinradarResult;

typedef struct BinradarManager {
    uint32_t patch_cnt;
    int patch_fd_r;
    uint32_t *cur_patch_id; // Shared memory
    uint32_t *cur_iter; // Shared memory
    sbsv_parser *patch_result_parser;
    GPtrArray *results; // Array<BinradarResult *>
    BinradarResult *current; // For temp use before write to results array
    size_t line_idx;
    char line_buf[4096];
    // Candidate patch ids (survived patches from filter.sbsv), length patch_cnt.
    // NULL means candidates are 1..patch_cnt.
    uint32_t *patch_list;
    // Max patch id that can be indexed in patch_results (allocated size = patch_max_id + 1).
    uint32_t patch_max_id;
} BinradarManager;

static SharedTraceData *shared_trace_data = NULL;
/* OSPREY in-process structural type analysis (Stage 1: shared-run fact
 * transport).  The parent allocates one fixed-layout MAP_SHARED run and
 * resets it before each fork; the child attaches and the parent merges
 * the completed sample after waitpid. */
static OspreyContext *g_osprey_ctx = NULL;
static OspreySharedRun *g_osprey_shared_run = NULL;
static GList *binradar_protected_mappings = NULL;

static OrderedMap *g_read_access_tainted_primitives = NULL;
static OrderedMap *g_read_access_pointers = NULL;

static GHashTable *g_read_access_tainted_primitives_original = NULL;
static GHashTable *g_read_access_pointers_original = NULL;

static GHashTable *g_read_access_tainted_primitives_all = NULL;
static GHashTable *g_read_access_pointers_all = NULL;

static ModificationManager *mod_manager = NULL;
static SnapshotExitInfo original_exit_info;

static BinradarManager *binradar_manager = NULL;

static BinradarResult *binradar_manager_alloc_one_iter(BinradarManager *manager) {
    if (manager == NULL) return NULL;
    BinradarResult *result = g_new0(BinradarResult, 1);
    result->iter = 0;
    result->patch_results = g_new0(PatchedResult, manager->patch_max_id + 1);
    return result;
}

static void trace_mem_flush(void);
static int binradar_manager_cur_patch_id(BinradarManager *manager, int new_patch_id);
static int binradar_manager_cur_iter(BinradarManager *manager, int new_iter);
void parse_exclude_region_str(const char *name, uintptr_t load_bias, exclude_region *region);
bool is_e9_relocated_call(target_ulong pc, target_ulong *call_site,
                          target_ulong *ret_addr);

static int read_exact(int fd, void *buf, size_t len) {
    uint8_t *p = buf;
    size_t total = 0;

    while (total < len) {
        ssize_t n = read(fd, p + total, len - total);
        if (n == 0) {
            return -1;
        }
        if (n < 0) {
            if (errno == EINTR) {
                continue;
            }
            return -1;
        }
        total += (size_t)n;
    }

    return 0;
}

static int write_exact(int fd, const void *buf, size_t len) {
    const uint8_t *p = buf;
    size_t total = 0;

    while (total < len) {
        ssize_t n = write(fd, p + total, len - total);
        if (n < 0) {
            if (errno == EINTR) {
                continue;
            }
            return -1;
        }
        if (n == 0) {
            return -1;
        }
        total += (size_t)n;
    }

    return 0;
}

void parse_exclude_region_str(const char *name, uintptr_t load_bias, exclude_region *region) {
    if (name == NULL || region == NULL) {
        return;
    }
    // Expected format: "0x20e9e9000-0x20e9ea000"
    char *region_str = getenv(name);
    char *dash = strchr(region_str, '-');
    if (dash == NULL) {
        log_msg("[snapshot] [parse-exclude-region] [name %s] [invalid-format] %s\n", name, region_str ? region_str : "NULL");
        return;
    }
    *dash = '\0';
    region->start = strtoull(region_str, NULL, 16) + load_bias;
    region->end = strtoull(dash + 1, NULL, 16) + load_bias;
    log_msg("[snapshot] [parse-exclude-region] [name %s] [start %lx] [end %lx]\n", name, region->start, region->end);
}

static void check_env_var(const char *name) {
    char *value = getenv(name);
    if (value == NULL) {
        log_msg("[snapshot] [check-env-var] [name %s] [not-set]\n", name);
    } else {
        log_msg("[snapshot] [check-env-var] [name %s] [value %s]\n", name, value);
    }
}

void parse_e9_relocated_calls(uintptr_t load_bias) {
    // Expected format: "0x<jump>:0x<site>:0x<ret>,0x<jump>:0x<site>:0x<ret>,..."
    // One record per E9Patch CALLQ relocation: the address of the jump that
    // re-implements the call, the original call site, and the return address.
    char *value = getenv("E9_RELOCATED_CALL_JUMPS");
    if (value == NULL || value[0] == '\0') {
        return;
    }
    char *copy = g_strdup(value);
    char *saveptr = NULL;
    for (char *record = strtok_r(copy, ",", &saveptr); record != NULL;
         record = strtok_r(NULL, ",", &saveptr)) {
        char *jump_str = record;
        char *colon = strchr(record, ':');
        if (colon == NULL) {
            log_msg("[snapshot] [e9-relocated-call] [invalid-format] [record %s]\n", record);
            continue;
        }
        *colon = '\0';
        char *site_str = colon + 1;
        colon = strchr(site_str, ':');
        if (colon == NULL) {
            log_msg("[snapshot] [e9-relocated-call] [invalid-format] [record %s]\n", record);
            continue;
        }
        *colon = '\0';
        char *ret_str = colon + 1;

        if (e9_relocated_calls_len == e9_relocated_calls_cap) {
            e9_relocated_calls_cap = e9_relocated_calls_cap ? e9_relocated_calls_cap * 2 : 8;
            e9_relocated_calls = g_realloc(e9_relocated_calls,
                                           e9_relocated_calls_cap * sizeof(*e9_relocated_calls));
        }
        e9_relocated_calls[e9_relocated_calls_len].jump_addr =
            strtoull(jump_str, NULL, 16) + load_bias;
        e9_relocated_calls[e9_relocated_calls_len].call_site =
            strtoull(site_str, NULL, 16) + load_bias;
        e9_relocated_calls[e9_relocated_calls_len].ret_addr =
            strtoull(ret_str, NULL, 16) + load_bias;
        log_msg("[snapshot] [e9-relocated-call] [jump %lx] [site %lx] [ret %lx]\n",
                (unsigned long)e9_relocated_calls[e9_relocated_calls_len].jump_addr,
                (unsigned long)e9_relocated_calls[e9_relocated_calls_len].call_site,
                (unsigned long)e9_relocated_calls[e9_relocated_calls_len].ret_addr);
        e9_relocated_calls_len++;
    }
    g_free(copy);
}

bool is_e9_relocated_call(target_ulong pc, target_ulong *call_site,
                          target_ulong *ret_addr) {
    for (size_t i = 0; i < e9_relocated_calls_len; i++) {
        if (e9_relocated_calls[i].jump_addr == pc) {
            if (call_site != NULL) {
                *call_site = e9_relocated_calls[i].call_site;
            }
            if (ret_addr != NULL) {
                *ret_addr = e9_relocated_calls[i].ret_addr;
            }
            return true;
        }
    }
    return false;
}

void check_all_env_var(void) {
    // Log
    check_env_var("BINRADAR_TRACER_LOG_FILE");
    check_env_var("BINRADAR_TRACE_FILE");
    // Fuzzolic
    check_env_var("SYMBOLIC_INJECT_INPUT_MODE");
    check_env_var("SYMBOLIC_TESTCASE_NAME");
    check_env_var("PLT_INFO_FILE");
    // Forkserver releated
    check_env_var("BINRADAR_FORKSERVER_ENABLE");
    check_env_var("BINRADAR_ENTRYPOINT");
    check_env_var("BINRADAR_FORKSERVER_CTRL_R");
    check_env_var("BINRADAR_FORKSERVER_STAT_W");
    check_env_var("BINRADAR_FORKSERVER_TARGET_HIT_COUNT");
    check_env_var("BINRADAR_PRESERVE_CHILD_QUERIES");
    check_env_var("BINRADAR_PROBE_FILE");
    check_env_var("BINRADAR_QUERY_WINDOW_FILE");
    check_env_var("BINRADAR_FORKSERVER_CHILD_TIMEOUT");
    // Memcheck related
    check_env_var("BINRADAR_MEMCHECK_ENABLE");
    // Patch related
    check_env_var("BINRADAR_PATCH_FD_R");
    check_env_var("PATCH_FD"); // Used by brpatch
    check_env_var("PATCH_ID"); // Used by brpatch, 123456
    check_env_var("BINRADAR_PATCH_CNT");
    check_env_var("BINRADAR_PATCH_FILTER_FILE");
    // e9tool patch region related
    check_env_var("PATCH_RESERVE_RANGE");
    check_env_var("E9_TRAMPOLINE_RANGE");
    check_env_var("E9_LOADER_RANGE");
    // E9Patch relocated call jumps (jump-addr:call-site:ret-addr, comma separated)
    check_env_var("E9_RELOCATED_CALL_JUMPS");
    // Shared memory
    check_env_var("EXPR_POOL_SHM_KEY");
    check_env_var("QUERY_SHM_KEY");
    check_env_var("BITMAP_SHM_KEY");
    check_env_var("BINRADAR_PATCH_SHM_KEY");
}

void add_exclude_regions(uintptr_t load_bias) {
    parse_exclude_region_str("PATCH_RESERVE_RANGE", load_bias, &binradar_exclude_regions[0]);
    parse_exclude_region_str("E9_TRAMPOLINE_RANGE", load_bias, &binradar_exclude_regions[1]);
    parse_exclude_region_str("E9_LOADER_RANGE", load_bias, &binradar_exclude_regions[2]);
}

bool is_in_exclude_region(target_ulong pc) {
    // Inserted patch should not exceed 1MB
    for (int i = 0; i < 3; i++) {
        exclude_region *region = &binradar_exclude_regions[i];
        if (pc >= region->start && pc < region->end) {
            return true;
        }
    }
    return false;
}

void snapshot_protect_mapping(target_ulong addr, target_ulong len) {
    if (addr == (target_ulong)-1 || len == 0) {
        return;
    }
    SnapshotMapping *map = g_new(SnapshotMapping, 1);
    map->start = addr;
    map->len = len;
    binradar_protected_mappings = g_list_prepend(binradar_protected_mappings, map);
}

bool snapshot_addr_is_protected(target_ulong addr) {
    for (GList *node = binradar_protected_mappings; node != NULL; node = node->next) {
        SnapshotMapping *map = (SnapshotMapping *)node->data;
        if (map == NULL) {
            continue;
        }
        if (addr >= map->start && addr < map->start + map->len) {
            return true;
        }
    }
    return false;
}

static void exit_with_status(int status) {
    trace_mem_flush();
    exit(status);
}

static void binradar_manager_load_filter(BinradarManager *manager, const char *path) {
    FILE *fp = fopen(path, "r");
    if (fp == NULL) {
        log_msg("[binradar] [patch-filter] [error] cannot open filter file: %s\n", path);
        return;
    }
    sbsv_parser *parser = sbsv_parser_new(SBSV_PARSER_DEFAULT);
    sbsv_parser_add_schema(parser, "[patch] [id: int] [pass: bool]");
    sbsv_status status = sbsv_parser_load_file(parser, fp);
    fclose(fp);
    if (status != SBSV_OK) {
        log_msg("[binradar] [patch-filter] [error] failed to parse filter file: %s [status %s]\n",
                path, sbsv_status_str(status));
        sbsv_parser_free(parser);
        return;
    }
    const sbsv_row **rows = NULL;
    size_t count = 0;
    if (sbsv_parser_get_rows(parser, "patch", &rows, &count) != SBSV_OK) {
        log_msg("[binradar] [patch-filter] [error] failed to get patch rows: %s\n", path);
        sbsv_parser_free(parser);
        return;
    }
    GArray *ids = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    uint32_t max_id = 0;
    for (size_t i = 0; i < count; i++) {
        long long id = sbsv_row_get_int(rows[i], "id", NULL);
        int pass = sbsv_row_get_bool(rows[i], "pass", NULL);
        if (pass && id > 0 && (uint64_t)id <= UINT32_MAX) {
            uint32_t patch_id = (uint32_t)id;
            g_array_append_val(ids, patch_id);
            if (patch_id > max_id) {
                max_id = patch_id;
            }
        }
    }
    sbsv_free_row_ref_array(rows);
    sbsv_parser_free(parser);
    if (ids->len == 0) {
        log_msg("[binradar] [patch-filter] [no-survivors] [file %s]\n", path);
        manager->patch_cnt = 0;
        manager->patch_max_id = 0;
        g_array_free(ids, TRUE);
        return;
    }
    manager->patch_list = g_new(uint32_t, ids->len);
    for (guint i = 0; i < ids->len; i++) {
        manager->patch_list[i] = g_array_index(ids, uint32_t, i);
    }
    manager->patch_cnt = ids->len;
    manager->patch_max_id = max_id;
    g_array_free(ids, TRUE);
    log_msg("[binradar] [patch-filter] [file %s] [cnt %u] [max-id %u]\n",
            path, manager->patch_cnt, manager->patch_max_id);
    for (uint32_t i = 0; i < manager->patch_cnt; i++) {
        log_msg("[binradar] [patch-filter] [id %u]\n", manager->patch_list[i]);
    }
}

void snapshot_set_binradar_patch_shm(uint32_t *shm) {
    binradar_manager = g_new0(BinradarManager, 1);
    binradar_manager->patch_cnt = 1;
    binradar_manager->results = g_ptr_array_new();
    binradar_manager->cur_patch_id = shm;
    *binradar_manager->cur_patch_id = 0;
    binradar_manager->cur_iter = shm + 1;
    *binradar_manager->cur_iter = 0;
    char *var = getenv("BINRADAR_PATCH_FD_R");
    if (var != NULL) {
        binradar_manager->patch_fd_r = atoi(var);
    } else {
        log_msg("BINRADAR_PATCH_FD_R not set");
        exit_with_status(1);
    }
    var = getenv("BINRADAR_PATCH_CNT");
    if (var != NULL) {
        binradar_manager->patch_cnt = atoi(var);
    } else {
        log_msg("BINRADAR_PATCH_CNT not set");
        exit_with_status(1);
    }
    binradar_manager->patch_list = NULL;
    binradar_manager->patch_max_id = binradar_manager->patch_cnt;
    var = getenv("BINRADAR_PATCH_FILTER_FILE");
    if (var != NULL && var[0] != '\0') {
        binradar_manager_load_filter(binradar_manager, var);
    }
    binradar_manager->current = binradar_manager_alloc_one_iter(binradar_manager);
    binradar_manager->patch_result_parser = sbsv_parser_new(SBSV_PARSER_DEFAULT);
    sbsv_parser_add_schema(binradar_manager->patch_result_parser, "[patch] [id: int] [br: int] [v: int]");
}

static void snapshot_load_binradar_env(void) {
    if (binradar_forkserver_enable != -1) return;

    binradar_forkserver_enable      = 1;
    binradar_preserve_child_queries = 0;
    binradar_solver_mutation_mode = 0;

    const char* var = getenv("BINRADAR_FORKSERVER_ENABLE");
    if (var) {
        binradar_forkserver_enable = atoi(var) != 0;
    }

    var = getenv("BINRADAR_FORKSERVER_CTRL_R");
    if (var) {
        binradar_forkserver_ctrl_r = atoi(var);
    }
    var = getenv("BINRADAR_FORKSERVER_STAT_W");
    if (var) {
        binradar_forkserver_stat_w = atoi(var);
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

    binradar_probe_file = getenv("BINRADAR_PROBE_FILE");
    if (binradar_probe_file && binradar_probe_file[0] == '\0') {
        binradar_probe_file = NULL;
    }

    binradar_query_window_file = getenv("BINRADAR_QUERY_WINDOW_FILE");
    if (binradar_query_window_file && binradar_query_window_file[0] == '\0') {
        binradar_query_window_file = NULL;
    }

    var = getenv("BINRADAR_MEMCHECK_ENABLE");
    if (var) {
        binradar_memcheck_enabled = atoi(var) != 0;
    }
    log_msg("[snapshot-load-binradar] [forkserver %d] [hit-count %lu] [probe-file %s] [query-window-file %s] [memcheck %d]\n",
              binradar_forkserver_enable, binradar_forkserver_target_hit_count,
              binradar_probe_file ? binradar_probe_file : "null",
              binradar_query_window_file ? binradar_query_window_file : "null",
              binradar_memcheck_enabled);
}

static void snapshot_dump_query_window(Query* q, Expr *e) {
    snapshot_load_binradar_env();
    if (binradar_query_window_dumped || binradar_query_window_file == NULL) {
        return;
    }

    int64_t start_index = GET_QUERY_IDX(next_query);
    int64_t end_index = GET_QUERY_IDX(q);
    // Preserve query window for first run
    next_query = q;
    next_free_expr = e;

    FILE *fp = fopen(binradar_query_window_file, "a");
    if (fp == NULL) {
        fprintf(stderr, "Failed to open binradar query window file: %s\n", binradar_query_window_file);
        return;
    }

    fprintf(fp, "[query-window] [start %ld] [end %ld]\n", start_index, end_index - 1);
    fclose(fp);
    binradar_query_window_dumped = 1;
}

uint8_t snapshot_on_entrypoint_hit(target_ulong pc) {
    snapshot_load_binradar_env();
    binradar_entrypoint_hit_count += 1;

    log_msg("[snapshot] [entrypoint-hit] [pc %lx] [count %lu] [target %lu]\n",
              pc, binradar_entrypoint_hit_count,
              binradar_forkserver_target_hit_count);

    if (!binradar_forkserver_enable) return 0;
    if (binradar_forkserver_target_hit_count == 0) return 0;
    return binradar_entrypoint_hit_count == binradar_forkserver_target_hit_count;
}


static int use_trace = -1;
static int trace_fd = -1;
static int use_log = -1;
static int log_fd = -1;

static void trace_mem_init(void) {
    if (use_trace != -1) return;
    char* trace_file = getenv("BINRADAR_TRACE_FILE");
    if (trace_file == NULL) {
        use_trace = 1;
        trace_fd = STDERR_FILENO;
    } else if (strcmp(trace_file, "none") == 0) {
        use_trace = 0;
    } else {
        use_trace = 1;
        trace_fd = open(trace_file, O_WRONLY | O_CREAT | O_APPEND, 0644);
        if (trace_fd < 0) {
            fprintf( stderr, "ERROR: cannot open trace file %s\n",
                    trace_file);
            exit_with_status(1);
        }
    }
}

static void log_msg_init(void) {
    if (use_log != -1) return;
    char* log_file = getenv("BINRADAR_TRACER_LOG_FILE");
    if (log_file == NULL) {
        use_log = 1;
        log_fd = STDERR_FILENO;
    } else if (strcmp(log_file, "none") == 0) {
        use_log = 0;
    } else {
        use_log = 1;
        log_fd = open(log_file, O_WRONLY | O_CREAT | O_APPEND, 0644);
        if (log_fd < 0) {
            fprintf( stderr, "ERROR: cannot open log file %s\n",
                    log_file);
            exit_with_status(1);
        }
    }
}

void trace_mem(const char* fmt, ...) {
    trace_mem_init();
    if (!use_trace)
        return;
    if (mod_manager != NULL) {
        // Don't write after type analysis is done
        return;
    }
    va_list ap;
    char buf[4096];
    va_start(ap, fmt);
    int n = vsnprintf(buf, sizeof(buf), fmt, ap);
    va_end(ap);
    ssize_t wr;
    if (n < 0) {
        return;
    }
    if (n >= sizeof(buf)) {
        // This should not happen
        wr = write(trace_fd, buf, sizeof(buf) - 1);
        wr = write(trace_fd, "\n[ERROR] [TRUNCATED]\n", 21);
    } else {
        wr = write(trace_fd, buf, n);
    }
    (void)wr;
}

void log_msg(const char* fmt, ...) {
    log_msg_init();
    if (!use_log)
        return;
    va_list ap;
    char buf[4096];
    va_start(ap, fmt);
    int n = vsnprintf(buf, sizeof(buf), fmt, ap);
    va_end(ap);
    ssize_t wr;
    if (n < 0) {
        return;
    }
    if (n >= sizeof(buf)) {
        // This should not happen
        wr = write(log_fd, buf, sizeof(buf) - 1);
        wr = write(log_fd, "\n[ERROR] [TRUNCATED]\n", 21);
    } else {
        wr = write(log_fd, buf, n);
    }
    (void)wr;
}

void trace_mem_flush(void) {
    if (!use_trace) return;
    if (trace_fd > 2)
        fsync(trace_fd);
}

static void log_msg_flush(void) {
    if (!use_log) return;
    if (log_fd > 2)
        fsync(log_fd);
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
    OrderedMapEntry *existing = g_hash_table_lookup(map->table, GSIZE_TO_POINTER(key));
    int old_index = -1;
    if (existing != NULL) {
        old_index = existing->shared_index;
        g_queue_delete_link(map->queue, existing->node);
        g_hash_table_remove(map->table, GSIZE_TO_POINTER(key));
    }

    if (map->max_size > 0 && g_queue_get_length(map->queue) >= map->max_size) {
        OrderedMapEntry *oldest_entry = (OrderedMapEntry *)g_queue_pop_head(map->queue);
        if (oldest_entry != NULL) {
            old_index = oldest_entry->shared_index;
            uintptr_t old_key = oldest_entry->key;
            g_hash_table_remove(map->table, GSIZE_TO_POINTER(old_key));
        }
    }

    OrderedMapEntry *entry = g_new(OrderedMapEntry, 1);
    memset(entry, 0, sizeof(OrderedMapEntry));
    entry->key = key;
    entry->data = data;
    entry->shared_index = old_index;

    g_queue_push_tail(map->queue, entry);
    entry->node = map->queue->tail;
    g_hash_table_insert(map->table, GSIZE_TO_POINTER(key), entry);
    return entry;
}

OrderedMapEntry* ordered_map_lookup(OrderedMap *map, uintptr_t key) {
    OrderedMapEntry *entry = (OrderedMapEntry *)g_hash_table_lookup(map->table, GSIZE_TO_POINTER(key));
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

static int64_t snapshot_query_cursor_index(const SnapshotExitInfo *info) {
    return info != NULL && info->next_query != NULL && query_queue != NULL
        ? (int64_t)(info->next_query - query_queue) : -1;
}

static int64_t snapshot_expr_cursor_index(const SnapshotExitInfo *info) {
    return info != NULL && info->next_free_expr != NULL && pool != NULL
        ? (int64_t)(info->next_free_expr - pool) : -1;
}

static void snapshot_log_cursor_indices(const SnapshotExitInfo *info) {
    log_msg("[snapshot] [cursors] [query_cursor %ld] [expr_cursor %ld]\n",
            snapshot_query_cursor_index(info),
            snapshot_expr_cursor_index(info));
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
    /* Deferred provenance finding: finalize as a synthetic crash unless a
     * real crash already won the exit-info slot (deterministic precedence,
     * FIX_TRACER.md §8 / test 21). */
	if (provenance_finalize_fault(cpu_env)) {
		ProvPublishedFinding fault;
		if (!provenance_snapshot_pending_finding(&fault)) {
			/* Finding disappeared between finalize and snapshot. */
			return;
		}
		const char *pf_reason = provenance_fault_reason();
		/* Emit the structured finding exactly once, even when a real
		 * crash already won the exit-info slot: §8 requires preserving
		 * BOTH records (the pending provenance event and the real
		 * signal), with the real crash selecting the verdict. */
		provenance_report_pending_finding();

		SnapshotExitInfo *info = snapshot_exit_info_ptr();
		if (info->valid && info->crashed) {
			/* Real crash already recorded — the earlier record wins the
			 * verdict; the finding was preserved above. */
			return;
		}
		snapshot_record_guest_crash(cpu_env, TARGET_SIGSEGV, 0,
		                            SEGV_ACCERR, fault.payload.access_pc, 0,
		                            pf_reason);
		/* Crash record stores fault_addr = guest_pc (code address).
		 * Re-expose the provenance access PC for diagnostics. */
		info = snapshot_exit_info_ptr();
		info->fault_addr = fault.payload.access_pc;
		return;
	}

    SnapshotExitInfo *info = snapshot_exit_info_ptr();
    if (!snapshot_exit_info_should_update(info, false)) return;
    info->valid = 1;
    info->crashed = 0;
    info->exit_code = exit_code;
    snapshot_exit_info_capture(info, cpu_env);
    snapshot_exit_info_set_reason(info, reason ? reason : "normal_exit");
	log_msg("[snapshot] [exit] [normal] [entrypoint-hit %lu]\n",
	        binradar_entrypoint_hit_count);
	snapshot_log_cursor_indices(info);
    if (binradar_manager) {
        int patch_id = binradar_manager_cur_patch_id(binradar_manager, -1);
        int iter = binradar_manager_cur_iter(binradar_manager, -1);
        log_msg("[binradar] [normal] [iter %d] [patch %d] [guest_pc %lx] [guest_cs_base %lx] [reason %s]\n",
                  iter, patch_id, info->guest_pc, info->guest_cs_base, reason ? reason : "normal_exit");
    }
    
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
    info->host_fault_addr = host_fault_addr;
    snapshot_exit_info_capture(info, cpu_env);
    /* The binradar comparison matches this against the probe's [fault-addr],
     * which is a code address (the faulting instruction).  Store guest_pc
     * here rather than the siginfo data address so both sides agree. */
    info->fault_addr = info->guest_pc;
    char buffer[SNAPSHOT_EXIT_DESC_LEN];
    const char *base = reason ? reason : "unhandled signal";
    const char *host_name = (host_signal > 0) ? strsignal(host_signal) : NULL;
    if (host_name) {
        g_snprintf(buffer, sizeof(buffer), "%s (host=%s[%d], target=%d)", base, host_name, host_signal, target_signal);
    } else {
        g_snprintf(buffer, sizeof(buffer), "%s (host=%d, target=%d)", base, host_signal, target_signal);
    }
    snapshot_exit_info_set_reason(info, buffer);
	log_msg("[snapshot] [exit] [crash] [entrypoint-hit %lu]\n",
	        binradar_entrypoint_hit_count);
	snapshot_log_cursor_indices(info);
	log_msg("[snapshot] [crash] [hit-count %lu] [reason %s] [guest_pc %lx] [guest_cs_base %lx] [fault_addr %lx] [host_fault_addr %lx]\n",
	            binradar_entrypoint_hit_count, buffer, info->guest_pc, info->guest_cs_base, info->fault_addr, info->host_fault_addr);
    if (binradar_manager) {
        int patch_id = binradar_manager_cur_patch_id(binradar_manager, -1);
        int iter = binradar_manager_cur_iter(binradar_manager, -1);
        log_msg("[binradar] [crash] [iter %d] [patch %d] [guest_pc %lx] [guest_cs_base %lx] [fault_addr %lx] [host_fault_addr %lx] [reason %s]\n",
                  iter, patch_id, info->guest_pc, info->guest_cs_base, info->fault_addr, info->host_fault_addr, buffer);
    }
    
    if (binradar_probe_file) {
        FILE *binradar_probe_file_fp = fopen(binradar_probe_file, "a");
        if (binradar_probe_file_fp == NULL) {
            fprintf(stderr, "Failed to open binradar probe file: %s\n", binradar_probe_file);
            return;
        }
        fprintf(binradar_probe_file_fp, "[snapshot] [crash] [hit-count %lu] [reason %s] [guest_pc %lx] [guest_cs_base %lx] [fault_addr %lx] [host_fault_addr %lx]\n",
                binradar_entrypoint_hit_count, buffer, info->guest_pc, info->guest_cs_base, info->fault_addr, info->host_fault_addr);
        fclose(binradar_probe_file_fp);
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
    g_hash_table_remove(g_read_access_tainted_primitives->table, GSIZE_TO_POINTER(addr));
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
        exit_with_status(1);
    }
    ptr->addr = addr;
    ptr->target = target;
    ptr->pc = pc;
    ptr->access_id = __atomic_fetch_add(&shared_trace_data->ptr_access_cnt, 1, __ATOMIC_RELAXED);
    ptr->expr = NULL;
    entry->data = ptr;
    trace_mem("[rpo] [addr %lx] [target %lx] [pc %lx] [index %d] [id %ld]\n",
              addr, target, pc, entry->shared_index, ptr->access_id);
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
        exit_with_status(1);
    }
    prim->addr = addr;
    prim->size = size;
    prim->pc = pc;
    prim->access_id = __atomic_fetch_add(&shared_trace_data->prim_access_cnt, 1, __ATOMIC_RELAXED);
    prim->expr = NULL;
    entry->data = prim;
    trace_mem("[rpi] [addr %lx] [size %d] [pc %lx] [index %d] [id %ld]\n",
              addr, size, pc, entry->shared_index, prim->access_id);
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
    SnapshotPageInfo *info = g_hash_table_lookup(g_snapshot.pages, GSIZE_TO_POINTER(page));
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
    PendingAlloc alloc = {true, size, pc};
    g_array_append_val(stack, alloc);
    trace_mem("[alloc] [temp] [size %lx] [pc %lx]\n", size, pc);
}

PendingAlloc snapshot_trace_get_pending_allocs(target_ulong pc) {
    GArray *stack = get_pending_allocs();
    PendingAlloc result = {false, 0, 0};
    if (stack->len == 0) {
        // This should not happen
        return result;
    }
    result = g_array_index(stack, PendingAlloc, stack->len - 1);
    if (result.pc != pc) {
        result = (PendingAlloc){false, 0, 0};
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
    /* Heap/global regions are half-open: [base, base+size).  An access
     * exactly at base+size (one-past-end) is NOT inside. */
    if (mr->base + mr->size <= addr) return -1;
    if (mr->base > addr) return 1;
    return 0;
}

static target_ulong dyn_frame_low(const DynStackFrame *frame) {
    return frame ? frame->min_sp : 0;
}

static target_ulong dyn_frame_high(const DynStackFrame *frame) {
    return frame ? frame->entry_sp : 0;
}

static void dyn_frame_sync_region(DynStackFrame *frame) {
    if (frame == NULL) {
        return;
    }
    frame->region.is_heap = false;
    frame->region.is_stack = true;
    frame->region.base = frame->entry_sp;
    frame->region.size = frame->entry_sp >= frame->min_sp
        ? frame->entry_sp - frame->min_sp
        : 0;
    frame->region.pc = frame->frame_id;
}

static DynStackFrame *dyn_stack_top(void) {
    if (mr_manager.stack_data == NULL || mr_manager.stack_data->len == 0) {
        return NULL;
    }
    return g_array_index(mr_manager.stack_data, DynStackFrame *,
                         mr_manager.stack_data->len - 1);
}

static void dyn_stack_update_summary(void) {
    mr_manager.stack_region.is_heap = false;
    mr_manager.stack_region.is_stack = true;
    mr_manager.stack_region.pc = 0;

    if (mr_manager.stack_data == NULL || mr_manager.stack_data->len == 0) {
        mr_manager.stack_region.base = 0;
        mr_manager.stack_region.size = 0;
        return;
    }

    target_ulong high = 0;
    target_ulong low = (target_ulong)-1;
    for (guint i = 0; i < mr_manager.stack_data->len; i++) {
        DynStackFrame *frame = g_array_index(mr_manager.stack_data,
                                             DynStackFrame *, i);
        if (frame == NULL) {
            continue;
        }
        dyn_frame_sync_region(frame);
        if (frame->entry_sp > high) {
            high = frame->entry_sp;
        }
        if (frame->min_sp < low) {
            low = frame->min_sp;
        }
    }

    if (high == 0 || low == (target_ulong)-1 || low > high) {
        mr_manager.stack_region.base = 0;
        mr_manager.stack_region.size = 0;
        return;
    }
    mr_manager.stack_region.base = high;
    mr_manager.stack_region.size = high - low;
}

static bool dyn_frame_contains_access(const DynStackFrame *frame,
                                      target_ulong addr,
                                      target_ulong size) {
    if (frame == NULL || size == 0) {
        return false;
    }
    target_ulong end = addr + size;
    if (end < addr) {
        return false;
    }
    return addr >= dyn_frame_low(frame) && end <= dyn_frame_high(frame);
}

static bool dyn_frame_can_grow_for_access(const DynStackFrame *frame,
                                          target_ulong addr,
                                          target_ulong size) {
    if (frame == NULL || size == 0) {
        return false;
    }
    target_ulong end = addr + size;
    if (end < addr || end > frame->entry_sp || addr >= frame->min_sp) {
        return false;
    }
    return frame->min_sp - addr <= SNAPSHOT_STACK_LAZY_WINDOW;
}

static void dyn_stack_check_invariants(const char *where) {
    if (mr_manager.stack_data == NULL) {
        return;
    }

    for (guint i = 0; i < mr_manager.stack_data->len; i++) {
        DynStackFrame *frame = g_array_index(mr_manager.stack_data,
                                             DynStackFrame *, i);
        if (frame == NULL) {
            trace_mem("[stack-frame] [invariant-error] [where %s] "
                      "[depth %d] [reason null-frame]\n",
                      where ? where : "unknown", (int)i + 1);
            continue;
        }
        if (frame->frame_id == 0 || frame->min_sp > frame->entry_sp) {
            trace_mem("[stack-frame] [invariant-error] [where %s] "
                      "[fid %lx] [entry-sp %lx] [min-sp %lx] "
                      "[reason bad-frame-range]\n",
                      where ? where : "unknown",
                      (unsigned long)frame->frame_id, frame->entry_sp,
                      frame->min_sp);
        }

        if (i > 0) {
            DynStackFrame *caller = g_array_index(mr_manager.stack_data,
                                                  DynStackFrame *, i - 1);
            if (caller != NULL && caller->min_sp > frame->entry_sp) {
                trace_mem("[stack-frame] [invariant-error] [where %s] "
                          "[caller-fid %lx] [callee-fid %lx] "
                          "[caller-min-sp %lx] [callee-entry-sp %lx] "
                          "[reason caller-does-not-reach-call-sp]\n",
                          where ? where : "unknown",
                          (unsigned long)caller->frame_id,
                          (unsigned long)frame->frame_id,
                          caller->min_sp, frame->entry_sp);
            }
        }
    }
}

static void dyn_frame_grow_to_access(DynStackFrame *frame,
                                     target_ulong addr,
                                     target_ulong size,
                                     const char *reason) {
    if (frame == NULL) {
        return;
    }
    if (addr < frame->min_sp) {
        frame->min_sp = addr;
        frame->imprecise = true;
        dyn_frame_sync_region(frame);
        dyn_stack_update_summary();
        dyn_stack_check_invariants(reason);
        trace_mem("[stack-frame] [grow] [fid %lx] [addr %lx] [size %lx] "
                  "[entry-sp %lx] [min-sp %lx] [reason %s]\n",
                  (unsigned long)frame->frame_id, addr, size,
                  frame->entry_sp, frame->min_sp,
                  reason ? reason : "unknown");
    }
}

static void init_mr_manager(void) {
    mr_manager.stack_region.is_stack = true;
    if (mr_manager.stack_data == NULL) {
        mr_manager.stack_data = g_array_new(FALSE, FALSE, sizeof(DynStackFrame *));
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

static void mr_manager_heap_insert(SnapshotMemRegion *mr) {
    g_tree_insert(mr_manager.heap_data, mr, mr);
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
        // trace_mem("[mr] [heap] [error] failed to search region for [addr %lx]\n", addr);
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

    /* Lazily initialize the quarantine queue. */
    if (heap_quarantine == NULL) {
        heap_quarantine = g_queue_new();
    }

    /* Remove from cache (same as mr_manager_heap_remove). */
    int query_result = SNAPSHOT_MEM_REG_CACHE;
    while (query_result >= 0) {
        query_result = mr_manager_search_cache_exact(mr_manager.heap_cache, &query);
        mr_manager_update_cache(mr_manager.heap_cache, NULL, query_result);
    }

    /* Steal (not remove) from the heap tree so the SnapshotMemRegion is
     * not freed by g_tree_remove's key-destroy callback.  If the region
     * is not found, there is nothing to quarantine. */
    SnapshotMemRegion *mr = g_tree_search(mr_manager.heap_data,
                                          (GCompareFunc)search_region, &base);
    if (mr != NULL) {
        g_tree_steal(mr_manager.heap_data, mr);
        g_queue_push_tail(heap_quarantine, mr);
        heap_quarantine_bytes += mr->size;
        trace_mem("[free] [quarantine] [base %lx] [size %lx] [pc %lx] [total %lu]\n",
                  base, mr->size, pc, heap_quarantine_bytes);

        /* Evict oldest entries until under the byte cap. */
        while (heap_quarantine_bytes > HEAP_QUARANTINE_MAX_BYTES &&
               !g_queue_is_empty(heap_quarantine)) {
            SnapshotMemRegion *old = g_queue_pop_head(heap_quarantine);
            if (old != NULL) {
                heap_quarantine_bytes -= old->size;
                g_free(old);
            }
        }
    } else {
        trace_mem("[free] [error] [base %lx] [pc %lx] not exist\n", base, pc);
    }
}

static SnapshotMemRegion *mr_manager_stack_search(target_ulong addr,
                                                   target_ulong size) {
    GArray *stack = mr_manager.stack_data;
    if (stack == NULL || stack->len == 0 || size == 0) {
        return NULL;
    }

    for (ssize_t i = stack->len - 1; i >= 0; i--) {
        DynStackFrame *frame = g_array_index(stack, DynStackFrame *, i);
        if (frame == NULL) {
            continue;
        }
        dyn_frame_sync_region(frame);
        if (dyn_frame_contains_access(frame, addr, size)) {
#ifdef SNAPSHOT_STACK_TRACE_VERBOSE
            int64_t off = (int64_t)addr - (int64_t)frame->entry_sp;
            trace_mem("[stack-frame] [lookup] [fid %lx] [addr %lx] "
                      "[off %ld] [size %lx] [depth %d]\n",
                      (unsigned long)frame->frame_id, addr, (long)off,
                      size, (int)i + 1);
#endif
            return &frame->region;
        }
    }

    DynStackFrame *top = dyn_stack_top();
    if (dyn_frame_can_grow_for_access(top, addr, size)) {
        dyn_frame_grow_to_access(top, addr, size, "access-below-min-sp");
#ifdef SNAPSHOT_STACK_TRACE_VERBOSE
        int64_t off = (int64_t)addr - (int64_t)top->entry_sp;
        trace_mem("[stack-frame] [lookup-fallback] [fid %lx] [addr %lx] "
                  "[off %ld] [size %lx] [depth %d]\n",
                  (unsigned long)top->frame_id, addr, (long)off,
                  size, stack->len);
#endif
        return &top->region;
    }

#ifdef SNAPSHOT_STACK_TRACE_VERBOSE
    trace_mem("[stack-frame] [lookup-miss] [addr %lx] [size %lx] [depth %d]\n",
              addr, size, stack->len);
#endif
    return NULL;
}

void snapshot_trace_stack_call(target_ulong sp, target_ulong call_pc,
                               target_ulong ret_pc) {
    if (mr_manager.stack_data == NULL) {
        init_mr_manager();
    }

    DynStackFrame *caller = dyn_stack_top();
    if (caller != NULL && sp < caller->min_sp) {
        dyn_frame_grow_to_access(caller, sp, 1, "call-sp-below-caller-min");
    }

    DynStackFrame *frame = g_new0(DynStackFrame, 1);
    frame->frame_id = next_dyn_frame_id++;
    frame->entry_sp = sp;
    frame->min_sp = sp >= sizeof(target_ulong) ? sp - sizeof(target_ulong) : 0;
    frame->call_pc = call_pc;
    frame->ret_pc = ret_pc;
    dyn_frame_sync_region(frame);

    g_array_append_val(mr_manager.stack_data, frame);
    dyn_stack_update_summary();
    dyn_stack_check_invariants("push");

    trace_mem("[stack-frame] [push] [fid %lx] [entry-sp %lx] [min-sp %lx] "
              "[call-pc %lx] [ret-pc %lx] [depth %d]\n",
              (unsigned long)frame->frame_id, frame->entry_sp, frame->min_sp,
              frame->call_pc, frame->ret_pc, mr_manager.stack_data->len);

    /* Stack region identity: the frame's site key (call PC, else ret PC,
     * else the dynamic frame id) is the canonical stack region id for
     * OSPREY. */
    target_ulong legacy_pc = frame->call_pc != 0 ? frame->call_pc : frame->ret_pc;
    if (legacy_pc == 0) {
        legacy_pc = frame->frame_id;
    }
    trace_mem("[stack] [push] [sp %lx] [size %lx] [pc %lx] [depth %d] "
              "[sr-base %lx] [sr-size %lx]\n",
              frame->entry_sp, frame->region.size, legacy_pc,
              mr_manager.stack_data->len, mr_manager.stack_region.base,
              mr_manager.stack_region.size);
}

void snapshot_trace_stack_ret(target_ulong sp, target_ulong actual_ret_pc) {
    if (mr_manager.stack_data == NULL) {
        init_mr_manager();
    }

    GArray *stack = mr_manager.stack_data;
    if (stack->len == 0) {
        trace_mem("[stack-frame] [ret-miss] [sp %lx] [ret-pc %lx] [depth 0]\n",
                  sp, actual_ret_pc);
        return;
    }

    DynStackFrame *frame = g_array_index(stack, DynStackFrame *, stack->len - 1);
    if (frame == NULL) {
        trace_mem("[stack-frame] [ret-error] [sp %lx] [ret-pc %lx] "
                  "[depth %d] [reason null-top]\n",
                  sp, actual_ret_pc, stack->len);
        return;
    }

    if (frame->ret_pc != 0 && frame->ret_pc != actual_ret_pc) {
        frame->imprecise = true;
        trace_mem("[stack-frame] [ret-mismatch] [fid %lx] [expected %lx] "
                  "[actual %lx] [sp %lx] [depth %d]\n",
                  (unsigned long)frame->frame_id, frame->ret_pc,
                  actual_ret_pc, sp, stack->len);
    }

    if (sp < frame->entry_sp) {
        frame->imprecise = true;
        trace_mem("[stack-frame] [ret-sp-mismatch] [fid %lx] "
                  "[entry-sp %lx] [sp %lx] [ret-pc %lx] "
                  "[reason stack-not-unwound-to-entry]\n",
                  (unsigned long)frame->frame_id, frame->entry_sp, sp,
                  actual_ret_pc);
    } else if (sp > frame->entry_sp) {
        trace_mem("[stack-frame] [ret-sp-adjust] [fid %lx] "
                  "[entry-sp %lx] [sp %lx] [ret-pc %lx] "
                  "[delta %lx]\n",
                  (unsigned long)frame->frame_id, frame->entry_sp, sp,
                  actual_ret_pc, sp - frame->entry_sp);
    }

    trace_mem("[stack-frame] [pop] [fid %lx] [sp %lx] [entry-sp %lx] "
              "[min-sp %lx] [ret-pc %lx] [imprecise %d] [depth %d]\n",
              (unsigned long)frame->frame_id, sp, frame->entry_sp,
              frame->min_sp, actual_ret_pc, frame->imprecise,
              stack->len - 1);
    target_ulong legacy_pc = frame->call_pc != 0 ? frame->call_pc : frame->ret_pc;
    if (legacy_pc == 0) {
        legacy_pc = frame->frame_id;
    }
    trace_mem("[stack] [pop] [sp %lx] [base %lx] [pc %lx] [depth %d]\n",
              sp, frame->entry_sp, legacy_pc, stack->len - 1);

    g_array_set_size(stack, stack->len - 1);
    g_free(frame);
    dyn_stack_update_summary();
    dyn_stack_check_invariants("pop");
}

void snapshot_trace_stack_push(target_ulong sp, target_ulong pc) {
    snapshot_trace_stack_call(sp, 0, pc);
}

void snapshot_trace_stack_pop(target_ulong sp) {
    snapshot_trace_stack_ret(sp, 0);
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
    // trace_mem("[mr] [global] [search] [addr %lx]\n", addr);

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

    // trace_mem("[mr] [global] [error] failed to search region for [addr %lx]\n", addr);
    return NULL;
}

SnapshotMemRegion *snapshot_mem_region_search_with_size(target_ulong addr,
                                                        target_ulong size) {
    SnapshotMemRegion *mr = mr_manager_stack_search(addr, size);
    if (mr != NULL) {
        return mr;
    }

    mr = mr_manager_global_search(addr);
    if (mr != NULL) {
        return mr;
    }

    mr = mr_manager_heap_search(addr);
    if (mr != NULL) {
        return mr;
    }
    return NULL;
}

SnapshotMemRegion *snapshot_mem_region_search(target_ulong addr) {
    return snapshot_mem_region_search_with_size(addr, 1);
}

/* Check whether a memory access is within bounds of a known heap
 * allocation.
 *   MEMCHECK_OK        — access is within a valid heap region, or to
 *                        stack/global/unmapped memory (handled by MMU).
 *   MEMCHECK_HEAP_OOB  — access starts inside a heap region but extends
 *                        past its recorded end (exact-bounds overrun).
 *
 * Only exact-bounds overruns are reported. We deliberately do NOT
 * flag accesses that merely fall *near* (but outside) a recorded region:
 * the region tree is built from PLT-call-site malloc/free hooks and can
 * miss regions allocated through un-modelled entry points or by libraries,
 * so a "near a known region" heuristic produces false OOB reports on
 * accesses that actually belong to an adjacent, untracked allocation.
 * (This was the source of the pre-entrypoint memcheck crashes that broke
 * 23/30 benchmark subjects.) */
MemcheckResult snapshot_memcheck_access(target_ulong addr, target_ulong size) {
    /* UNKNOWN provenance: exact-bounds fallback on LIVE objects only.
     * Do NOT report UAF from numeric quarantine — UNKNOWN provenance
     * cannot distinguish a stale pointer from a valid pointer to a
     * reused or untracked allocation at the same address.  Provenance
     * identity, not address history, is required for UAF (§7). */
    SnapshotMemRegion *mr = mr_manager_heap_search_pub(addr);
    if (mr != NULL) {
        /* Half-open containment: mr->base <= addr < region_end.
         * The tree search guarantees this, so region_end - addr is
         * well-defined (no wrap).  Access is OOB when its full interval
         * exceeds the region end. */
        target_ulong region_end = mr->base + mr->size;
        if (region_end >= mr->base &&
            addr < region_end &&
            (uint64_t)size > (uint64_t)(region_end - addr)) {
            return MEMCHECK_HEAP_OOB;
        }
    }
    return MEMCHECK_OK;
}

/* Runtime helper called from instrumented TCG code (non-symbolic mode).
 * Routes through the provenance checker with an UNKNOWN tag; the
 * provenance checker applies the exact-bounds fallback on LIVE objects
 * and records a non-fatal pending finding (deferred crash policy, §8).
 * This helper must NOT call _exit(): the raw-TCG pass inserts it AFTER the
 * guest memory op (so a real fault raises first, §4/§9), and it must not
 * terminate execution itself.  The finding is finalized at guest exit. */
void snapshot_memcheck_helper(target_ulong addr, target_ulong size, target_ulong pc) {
    if (!binradar_memcheck_enabled) return;
    if (symbolic_start_code > 0 && (pc < symbolic_start_code || pc >= symbolic_end_code)) {
        return;
    }
    CPUState *cpu = thread_cpu;
    CPUArchState *env = cpu ? cpu->env_ptr : NULL;
    if (!env) return;
    PtrTag unknown_tag = {0};
    /* The finding is recorded as non-fatal (pending).  Do not _exit here:
     * the raw-TCG pass inserts this helper AFTER the qemu_ld/st, so a
     * faulting access has already raised before this helper runs (§4/§9).
     * The deferred finalize path converts pending findings to synthetic
     * crashes at guest exit. */
    provenance_check_access(env, addr, size, pc, unknown_tag, -1, 0);
}

/* Forward declaration: defined in tcg/symbolic/symbolic.c */
void memcheck_init(void);

bool snapshot_is_taken(void) {
    // return g_snapshot.is_snapshot_taken;
    return true;
}

void snapshot_init(void) {
    memset(&mr_manager, 0, sizeof(SnapshotMemRegionManager));
    next_dyn_frame_id = 1;
    init_mr_manager();
    memset(&g_snapshot, 0, sizeof(SnapshotState));
    g_snapshot.pages = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
    g_snapshot.is_snapshot_taken = false;
    // g_snapshot.cpu_state = malloc(sizeof(CPUArchState));
    // memset(g_snapshot.cpu_state, 0, sizeof(CPUArchState));
    size_t shm_size = sizeof(SharedTraceData);
    shared_trace_data = mmap(NULL, shm_size, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (shared_trace_data == MAP_FAILED) {
        log_msg("mmap shared memory failed");
        exit_with_status(1);
    }
    memset(shared_trace_data, 0, shm_size);
    /* Load binradar env vars early so binradar_memcheck_enabled is set
     * before any memory access instrumentation runs. */
    snapshot_load_binradar_env();
    /* Initialize PLT hooks for memcheck-only mode. */
    memcheck_init();
    /* OSPREY: parse config; when enabled, allocate the shared run and
     * arm the translator-side collection flag. */
    if (g_osprey_ctx == NULL) {
        OspreyConfig osprey_config;
        if (osprey_config_from_env(&osprey_config)) {
            g_osprey_ctx = osprey_new(&osprey_config);
            osprey_collect_enabled = osprey_config.enabled ? 1 : 0;
        }
    }
    if (g_osprey_ctx != NULL && g_osprey_ctx->config.enabled &&
        g_osprey_shared_run == NULL) {
        size_t run_size = osprey_shared_run_size(&g_osprey_ctx->config);
        void *run_mem = mmap(NULL, run_size, PROT_READ | PROT_WRITE,
                             MAP_SHARED | MAP_ANONYMOUS, -1, 0);
        if (run_mem == MAP_FAILED) {
            log_msg("[osprey] [fatal] shared run mmap failed\n");
            exit_with_status(1);
        }
        g_osprey_shared_run = run_mem;
        osprey_shared_run_reset(g_osprey_shared_run, 0,
                                &g_osprey_ctx->config);
        osprey_child_use_shared_run(g_osprey_ctx, g_osprey_shared_run);
        log_msg("[osprey] [init] [shared-mb %zu] [run-bytes %zu]\n",
                g_osprey_ctx->config.shared_bytes / (1024u * 1024u),
                run_size);
    }
    /* Deferred provenance findings live in the shared mmap so the parent
     * can read them after waitpid even on timeout/SIGKILL. */
    provenance_set_shared_fault_ptr(&shared_trace_data->prov_pending_fault);
    provenance_init();
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
            uint64_t key = addr & SNAPSHOT_PAGE_MASK;
            
            void *host_addr = g2h(addr);
            // memcpy(info->data, host_addr, SNAPSHOT_PAGE_SIZE);

            g_hash_table_insert(g_snapshot.pages, GSIZE_TO_POINTER(key), info);
            trace_mem("[snapshot] [memwalk] [addr %lx] [perms %ld] [host %lx]\n", (uint64_t)addr, flags, (uint64_t)host_addr);
        }
    }
    return 0;
}

void snapshot_save(void) {
    if (g_snapshot.pages == NULL) snapshot_init();
    if (g_snapshot.is_snapshot_taken) return;
    log_msg("[snapshot] [mem] [start]\n");
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
    log_msg("[snapshot] [result] [brk %llx] [mmap %llx] [pages %d]\n", (long long int)target_brk, (long long int)mmap_next_start, g_hash_table_size(g_snapshot.pages));
    dump_coverage_edge_log(false);

    /* OSPREY Stage 2.1: freeze the pre-snapshot prefix.  Every fact
     * collected before the snapshot (entrypoint frame, init-time
     * frames) becomes the frozen prefix family; the baseline child
     * contributes the post-snapshot suffix.  The merge treats
     * `prefix ∪ baseline-child` as exactly one unmodified sample.
     * Idempotent: snapshot_save runs once. */
    if (g_osprey_ctx != NULL && g_osprey_shared_run != NULL &&
        g_osprey_ctx->config.enabled) {
        osprey_shared_run_freeze_prefix(g_osprey_ctx, g_osprey_shared_run);
    }
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
            trace_mem("[snapshot] [raccess] [pointer] [addr %lx] [target %lx] [pc %lx]\n", addr, target, mem_access->pc);
        } else if (target == 0) {
            // It may be a null pointer
            add_read_access_primitive(addr, size, mem_access->pc);
            trace_mem("[snapshot] [raccess] [null-pointer] [addr %lx] [pc %lx]\n", addr, mem_access->pc);
            is_value_pointer = true; // Do not add it twice
        } else {
            trace_mem("[snapshot] [raccess] [primitive] [addr %lx] [value %lx] [pc %lx]\n", addr, target, mem_access->pc);
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
static target_ulong last_brk_end;  /* previous brk end (for shrink detection) */
void snapshot_syscall(CPUArchState *env, uintptr_t syscall_no,
                      uintptr_t syscall_arg0, uintptr_t syscall_arg1,
                      uintptr_t syscall_arg2, uintptr_t syscall_arg3,
                      uintptr_t syscall_arg4, uintptr_t syscall_arg5,
                      uintptr_t syscall_arg6, uintptr_t ret_val) {
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
            /* Provenance: kernel wrote into the buffer — stale shadow
             * entries must not be reloaded (FIX_TRACER.md test 18). */
            sem_mem_overwrite(env, syscall_arg1, ret_val, SEM_OP_SYSCALL);
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
#if defined(TARGET_NR_futex)
    case TARGET_NR_futex: // Fast user mutex
        // futex(uaddr, op, val, timeout, uaddr2, val3)
        // This QEMU version implements WAIT/WAKE/REQUEUE/CMP_REQUEUE and
        // WAKE_OP only.  Of those, only WAKE_OP writes guest memory: its
        // encoded atomic operation updates the 32-bit word at uaddr2.
        if ((long)ret_val >= 0) {
            uint32_t op = (uint32_t)syscall_arg1 & FUTEX_CMD_MASK;
            if (op == FUTEX_WAKE_OP) {
                if (syscall_arg4) {
                    sem_mem_overwrite(env, syscall_arg4, sizeof(uint32_t), SEM_OP_SYSCALL);
                }
            }
        }
        break;
#endif
#if defined(TARGET_NR_newfstatat)
    case TARGET_NR_newfstatat: // newfstatat(dirfd, pathname, statbuf, flags)
        // Kernel wrote sizeof(struct target_stat) bytes on success only.
        if ((long)ret_val == 0) {
            sem_mem_overwrite(env, syscall_arg2, sizeof(struct target_stat), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_fstatat64)
    case TARGET_NR_fstatat64:
        if ((long)ret_val == 0) {
            sem_mem_overwrite(env, syscall_arg2, sizeof(struct target_stat64), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_stat) || defined(TARGET_NR_lstat) || defined(TARGET_NR_fstat)
    case TARGET_NR_stat:
    case TARGET_NR_lstat:
    case TARGET_NR_fstat:
        // stat(pathname, statbuf) / lstat / fstat(fd, statbuf)
        if ((long)ret_val == 0) {
            sem_mem_overwrite(env, syscall_arg1, sizeof(struct target_stat), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_statx)
    case TARGET_NR_statx: // statx(dirfd, pathname, flags, mask, statxbuf)
        if ((long)ret_val == 0) {
            sem_mem_overwrite(env, syscall_arg4, sizeof(struct target_statx), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_statfs) || defined(TARGET_NR_fstatfs)
    case TARGET_NR_statfs:
    case TARGET_NR_fstatfs:
        // statfs(path, buf) / fstatfs(fd, buf)
        if ((long)ret_val == 0) {
            sem_mem_overwrite(env, syscall_arg1, sizeof(struct target_statfs), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_readlink)
    case TARGET_NR_readlink: // readlink(pathname, buf, bufsiz)
        // Kernel wrote ret bytes (the link length, no NUL).
        if ((long)ret_val > 0) {
            sem_mem_overwrite(env, syscall_arg1, ret_val, SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_readlinkat)
    case TARGET_NR_readlinkat: // readlinkat(dirfd, pathname, buf, bufsiz)
        if ((long)ret_val > 0) {
            sem_mem_overwrite(env, syscall_arg2, ret_val, SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_getrandom)
    case TARGET_NR_getrandom: // getrandom(buf, buflen, flags)
        if ((long)ret_val > 0) {
            sem_mem_overwrite(env, syscall_arg0, ret_val, SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_gettimeofday)
    case TARGET_NR_gettimeofday: // gettimeofday(tv, tz)
        // QEMU's linux-user implementation writes only the timeval and
        // deliberately passes NULL for the obsolete timezone argument.
        if ((long)ret_val == 0) {
            if (syscall_arg0) {
                sem_mem_overwrite(env, syscall_arg0,
                                         sizeof(struct target_timeval), SEM_OP_SYSCALL);
            }
        }
        break;
#endif
#if defined(TARGET_NR_clock_gettime)
    case TARGET_NR_clock_gettime: // clock_gettime(clockid, tp)
        // Kernel wrote struct timespec on success only.
        if ((long)ret_val == 0 && syscall_arg1) {
            sem_mem_overwrite(env, syscall_arg1,
                                     sizeof(struct target_timespec), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_clock_getres)
    case TARGET_NR_clock_getres: // clock_getres(clockid, res)
        if ((long)ret_val == 0 && syscall_arg1) {
            sem_mem_overwrite(env, syscall_arg1,
                                     sizeof(struct target_timespec), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_getdents)
    case TARGET_NR_getdents: // getdents(fd, dirp, count)
        // Kernel wrote ret bytes of dirent records into dirp.
        if ((long)ret_val > 0) {
            sem_mem_overwrite(env, syscall_arg1, ret_val, SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_getdents64)
    case TARGET_NR_getdents64: // getdents64(fd, dirp, count)
        // Kernel wrote ret bytes of dirent records into dirp.
        if ((long)ret_val > 0) {
            sem_mem_overwrite(env, syscall_arg1, ret_val, SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_recvfrom)
    case TARGET_NR_recvfrom: // recvfrom(fd, buf, len, flags, src_addr, addrlen)
        // Handled exactly at the copy-out site in do_recvfrom() (payload,
        // returned sockaddr, and the in/out addrlen word).  No-op here so
        // the source hook is the single owner of socket invalidation.
        break;
#endif
#if defined(TARGET_NR_recvmsg)
    case TARGET_NR_recvmsg: // recvmsg(fd, msg, flags)
        // Handled exactly at the copy-out site in do_sendrecvmsg_locked()
        // (payload iovecs, msg_name, control data, and the returned
        // msg_namelen/msg_controllen/msg_flags header fields).  No-op here.
        break;
#endif
    case TARGET_NR_brk: // heap adjustment
        // brk(new_brk_addr)
        // Handled in snapshot_restore
        trace_mem("New brk %lx received.\n", syscall_arg0);
        // On shrink (new brk below the previous end), stale shadow tags
        // in the unmapped tail must not be reloaded after regrowth.
        if ((long)ret_val < (long)last_brk_end) {
            sem_mem_overwrite(env, ret_val, last_brk_end - ret_val, SEM_OP_MAPPING);
        }
        last_brk_end = ret_val;
        break;
    // System call that changes heap shape:
    case TARGET_NR_mmap: // Memory map to file
        // mmap(addr, size, prot, flags, fd, offset) -> mapped addr
        snapshot_add_mapping(ret_val, syscall_arg1);
        // A fresh mapping must never inherit stale shadow entries (an
        // address previously used by another object).
        if ((long)ret_val > 0) {
            sem_mem_overwrite(env, ret_val, syscall_arg1, SEM_OP_MAPPING);
        }
        break;
    case TARGET_NR_mremap: // memory remap
        // mremap(old_addr, old_size, new_size, flags, new_addr) -> new addr
        // snapshot_remove_mapping(syscall_arg0, syscall_arg1);
        snapshot_add_mapping(ret_val, syscall_arg2);
        // Old range's shadow entries are stale (pages may be moved/freed).
        if ((long)ret_val >= 0) {
            sem_mem_overwrite(env, syscall_arg0, syscall_arg1, SEM_OP_MAPPING);
            if ((uintptr_t)ret_val != (uintptr_t)syscall_arg0) {
                sem_mem_overwrite(env, ret_val, syscall_arg2, SEM_OP_MAPPING);
            }
        }
        break;
    case TARGET_NR_munmap: // unmap
        // munmap(addr, length)
        // snapshot_remove_mapping(syscall_arg0, syscall_arg1);
        // Invalidate shadow for the unmapped range (stale tags must not
        // survive an address-space reuse).
        if ((long)ret_val == 0) {
            sem_mem_overwrite(env, syscall_arg0, syscall_arg1, SEM_OP_MAPPING);
        }
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
        if (g_hash_table_contains(g_snapshot.pages, GSIZE_TO_POINTER(p & SNAPSHOT_PAGE_MASK))) {
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
    log_msg("[forkserver] [setup]\n");
}

static abi_ulong snapshot_alloc_pointer_page(CPUArchState *env)
{
    abi_long mapped = target_mmap(0, SNAPSHOT_PAGE_SIZE,
                                  PROT_READ | PROT_WRITE,
                                  MAP_PRIVATE | MAP_ANONYMOUS,
                                  -1, 0);
    if (mapped == -1) {
        log_msg("[mod-pointer] [alloc-error] target_mmap failed\n");
        return (abi_ulong)-1;
    }

    memset(g2h((target_ulong)mapped), 0, SNAPSHOT_PAGE_SIZE);
    sem_mem_overwrite(env, (target_ulong)mapped, SNAPSHOT_PAGE_SIZE,
                      SEM_OP_SNAPSHOT);
    log_msg("[mod-pointer] [alloc] [addr %lx] [size %x]\n",
              (target_ulong)mapped, SNAPSHOT_PAGE_SIZE);
    return (abi_ulong)mapped;
}

// Modify guest program's state base on mod_manager (check analyze_collected_data)
static void mod_manager_init(SnapshotExitInfo *exit_info) {
    if (mod_manager == NULL) {
        mod_manager = g_new0(ModificationManager, 1);
        mod_manager->modifications = g_queue_new();
        mod_manager->done = g_array_new(FALSE, FALSE, sizeof(Modification *));
        mod_manager->mod_maps = g_hash_table_new(g_direct_hash, g_direct_equal);
        mod_manager->current = NULL;
        snapshot_dump_query_window(exit_info->next_query, exit_info->next_free_expr);
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
        log_msg("ERROR: empty modification\n");
        exit_with_status(1);
    }
    bool pointer_mod = false;
    for (int i = 0; i < mod->num_mods; i++) {
        if (mod->mods[i].kind == 1 && mod->mods[i].value_addr == 1) {
            pointer_mod = true;
            break;
        }
    }
    abi_ulong pointer_page = (abi_ulong)-1;
    if (pointer_mod) {
        log_msg("[mod-pointer] [start]\n");
        pointer_page = snapshot_alloc_pointer_page(cpu_env);
        if (pointer_page == (abi_ulong)-1) {
            log_msg("[mod-pointer] [error] failed to allocate pointer page\n");
            exit_with_status(1);
        }
    }
    for (int i = 0; i < mod->num_mods; i++) {
        MutationCandidate single_mod = mod->mods[i];
        if (single_mod.kind == 1 && single_mod.value_addr == 1) {
            target_ulong ptr_value = (target_ulong)pointer_page;
            memcpy(single_mod.value, &ptr_value, sizeof(target_ulong));
            if (single_mod.value_obj != NULL) {
                size_t obj_size = single_mod.size;
                if (obj_size > SNAPSHOT_PAGE_SIZE) {
                    obj_size = SNAPSHOT_PAGE_SIZE;
                }
                memcpy(g2h((target_ulong)pointer_page),
                       single_mod.value_obj, obj_size);
                sem_mem_overwrite(cpu_env, (target_ulong)pointer_page,
                                  obj_size, SEM_OP_SNAPSHOT);
            }
        }
        if (single_mod.addr < SNAPSHOT_PAGE_SIZE) {
            // Modify register
            target_ulong reg_value;
            memcpy(&reg_value, single_mod.value, sizeof(target_ulong));
            cpu_env->regs[(size_t)single_mod.addr] = reg_value;
            /* Register overwritten by modification → kill tag. */
            sem_reg_overwrite(cpu_env, (int)single_mod.addr,
                              SEM_OP_SNAPSHOT);
            log_msg("[mod-reg] [register %ld] [size %ld] [total %d]\n",
                      single_mod.addr,
                      single_mod.size,
                      g_queue_get_length(mod_manager->modifications));
            continue;
        }
        void *target_addr_h = g2h(single_mod.addr);
        memcpy(target_addr_h, single_mod.value, single_mod.size);
        /* Provenance: memory overwritten by modification → stale shadow
         * entries must not be reloaded (FIX_TRACER.md test 17). */
        sem_mem_overwrite(cpu_env, single_mod.addr, single_mod.size,
                          SEM_OP_SNAPSHOT);
        log_msg("[mod] [addr %lx] [size %ld] [total %d]\n", single_mod.addr, single_mod.size, g_queue_get_length(mod_manager->modifications));
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
    exit_with_status(128 + sig);
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

static void add_pointer_typed_candidate(GQueue *modifications,
                                        MutationCandidate *mod,
                                        const OspreyDecodedObject *pobj) {
    /* Type-inference candidate for a pointer-typed cell:
     *  - null value      -> pointee-typed object (fresh page, typed fill)
     *  - non-null value  -> null pointer and out-of-bounds pointer variants
     */
    target_ulong original;
    memcpy(&original, mod->value, sizeof(target_ulong));
    uint64_t raw = 0, extent = 0;
    if (!osprey_raw_extent(osprey_model(g_osprey_ctx), pobj, &raw, &extent)) {
        add_modification_primitive(modifications, mod);
        return;
    }
    if (original == 0) {
        /* NULL -> pointer to a freshly allocated object filled with valid
         * data; the modification machinery copies value_obj onto a new
         * pointer page and writes its address into the cell. */
        log_msg("[inferred] [pointee] [addr %lx] [extent %lu]\n",
                mod->addr, (unsigned long)extent);
        mod->value_addr = 1; /* dummy non-null value: allocate pointer page */
        mod->value_obj = g_malloc0(8);
        memset(mod->value_obj, 0, 8);
        g_queue_push_tail(modifications, add_single_modification(mod));
        memset(mod->value_obj, 1, 8);
        g_queue_push_tail(modifications, add_single_modification(mod));
        memset(mod->value_obj, 0xFF, 8);
        g_queue_push_tail(modifications, add_single_modification(mod));
    } else {
        /* valid pointer -> NULL */
        memset(mod->value, 0, sizeof(target_ulong));
        Modification *modification = add_single_modification(mod);
        g_queue_push_tail(modifications, modification);
        /* valid pointer -> out-of-bounds (extent past the object) */
        target_ulong oob = original + extent + 0x10;
        memcpy(mod->value, &oob, sizeof(target_ulong));
        modification = add_single_modification(mod);
        g_queue_push_tail(modifications, modification);
        log_msg("[inferred] [pointer-variants] [addr %lx] [orig %lx] "
                "[extent %lu]\n", mod->addr, original,
                (unsigned long)extent);
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

//     GArray *existing_mods = g_hash_table_lookup(manager->mod_maps, GSIZE_TO_POINTER(candidate->mods[0].addr));
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

static bool binradar_manager_check_addr(target_ulong addr) {
    if (snapshot_addr_is_protected(addr)) {
        log_msg("[binradar] [check-addr] [addr %lx] [hit]\n", addr);
        return true;
    }
    return false;
}



// In parent process, called after child execution
// Return: remaining modifications
static int select_next_modification(SnapshotExitInfo *exit_info) {
    (void)exit_info;

    if (mod_manager == NULL) {
        return 0;
    }

    if (mod_manager->current != NULL) {
        g_array_append_val(mod_manager->done, mod_manager->current);
    }
    mod_manager->current = g_queue_pop_head(mod_manager->modifications);
    if (mod_manager->current == NULL) {
        log_msg("[analyze] [done] consumed all modifications\n");
        if (shared_trace_data != NULL) {
            memset(shared_trace_data, 0, sizeof(SharedTraceData));
        }
        return 0;
    }

    // Finished: reset shared_trace_data
    memset(shared_trace_data, 0, sizeof(SharedTraceData));
    return g_queue_get_length(mod_manager->modifications) + 1;
}

static int analyze_collected_data(const ArgumentInfo *arg_info, size_t num_arg_regs) {
    if (shared_trace_data == NULL) {
        log_msg("Snapshot init error: shared_trace_data is null\n");
        exit_with_status(1);
    }
    // Analyze exit reason
    SnapshotExitInfo *exit_info = snapshot_exit_info_ptr();
    if (!exit_info || !exit_info->valid) {
        log_msg("[analyze] [exit-error] no exit info!!!\n");
        return 0;
    }
    bool is_crash = exit_info->crashed;
    if (is_crash) {
        const char *host_name =
                    (exit_info->host_signal > 0) ? strsignal(exit_info->host_signal) : NULL;
        if (exit_info->target_signal == 0) {
            log_msg("[analyze] [host-crash] [exit %d] [addr %lx] [reason %s] [name %s] [last %lx] Host crashed!!!\n", exit_info->host_signal, exit_info->host_fault_addr, exit_info->description, host_name ? host_name : "unknown", exit_info->guest_last_translation_block);
            exit_with_status(1);
        }
        log_msg("[analyze] [crash] [exit %d] [target %d] [host %d] [name %s] [fault-addr %lx] [guest-pc %lx] [guest-cs %lx] [si-code %d] [last %lx]\n", exit_info->exit_code, exit_info->target_signal, exit_info->host_signal, host_name ? host_name : "unknown", exit_info->fault_addr, exit_info->guest_pc, exit_info->guest_cs_base, exit_info->si_code, exit_info->guest_last_translation_block);
    } else {
        log_msg("[analyze] [normal] [exit %d] [guest-pc %lx] [guest-cs %lx] [reason %s] [last %lx]\n", exit_info->exit_code, exit_info->guest_pc, exit_info->guest_cs_base, exit_info->description, exit_info->guest_last_translation_block);
    }

    // Analyze shared_trace_data
    // Sort by access_id
    qsort(shared_trace_data->primitives, shared_trace_data->prim_idx, sizeof(PrimitiveAccess), compare_prim_id_desc);
    qsort(shared_trace_data->pointers, shared_trace_data->ptr_idx, sizeof(PointerAccess), compare_ptr_id_desc);
    GArray *mod_primitive_candidates = g_array_new(FALSE, FALSE, sizeof(MutationCandidate));
    // First run: collect all data
    if (mod_manager == NULL) {
        mod_manager_init(exit_info);
        
        memcpy(&original_exit_info, exit_info, sizeof(SnapshotExitInfo));
        g_read_access_tainted_primitives_original = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        g_read_access_pointers_original = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        g_read_access_tainted_primitives_all = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        g_read_access_pointers_all = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        // TODO: analyze added queries
        Query *query_top = exit_info->next_query;
        for (Query *q = next_query; q < query_top; q++) {
            log_msg("[analyze] [query] [op %s] [addr %lx]\n", opkind_to_str(q->query->opkind), q->address);
        }
        // TODO: Add function argument (register) access
        for (size_t i = 0; i < num_arg_regs; i++) {
            if (arg_info[i].expr) {
                if (is_valid_address(arg_info[i].value, false)) {
                    // Treat as pointer access
                    log_msg("[analyze] [sym-arg] [ptr] [reg %zu] [expr %lx]\n", i, arg_info[i].expr);
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
                    log_msg("[analyze] [sym-arg] [prim] [reg %zu] [expr %lx]\n", i, arg_info[i].expr);
                }
            }
        }
        
        // Create modification list
        for (int i = 0; i < shared_trace_data->prim_idx; i++) {
            PrimitiveAccess *prim = &shared_trace_data->primitives[i];
            PrimitiveAccess *prim_data = g_new(PrimitiveAccess, 1);
            memcpy(prim_data, prim, sizeof(PrimitiveAccess));
            g_hash_table_insert(g_read_access_tainted_primitives_original, GSIZE_TO_POINTER(prim_data->addr), prim_data);
            g_hash_table_insert(g_read_access_tainted_primitives_all, GSIZE_TO_POINTER(prim_data->addr), prim_data);
            log_msg("[analyze] [primitive] [index %d] [addr %lx] [size %d] [id %ld]\n", i, prim->addr, prim->size, prim->access_id);
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
            // Type inference (Stage 4): the decoded model maps raw
            // addresses to objects.  Pointer chunks get pointer-typed
            // candidates; everything else is a generic primitive.
            const OspreyDecodedObject *dobj = NULL;
            if (g_osprey_ctx != NULL) {
                const OspreyModel *pm = osprey_model(g_osprey_ctx);
                if (pm != NULL) {
                    dobj = osprey_lookup_raw(pm, (uint64_t)prim->addr);
                }
            }
            if (dobj != NULL && dobj->kind == OSPREY_DECODED_POINTER &&
                mod.size == sizeof(target_ulong)) {
                log_msg("[inferred] [pointer] [addr %lx] [size %d]\n",
                        prim->addr, prim->size);
                add_pointer_typed_candidate(mod_manager->modifications,
                                            &mod, dobj);
            } else {
                // No type information: apply generic modifications
                add_modification_primitive(mod_manager->modifications, &mod);
            }
        }
        for (int i = 0; i < shared_trace_data->ptr_idx; i++) {
            PointerAccess *ptr = &shared_trace_data->pointers[i];
            PointerAccess *ptr_data = g_new(PointerAccess, 1);
            memcpy(ptr_data, ptr, sizeof(PointerAccess));
            g_hash_table_insert(g_read_access_pointers_original, GSIZE_TO_POINTER(ptr_data->addr), ptr_data);
            g_hash_table_insert(g_read_access_pointers_all, GSIZE_TO_POINTER(ptr_data->addr), ptr_data);
            log_msg("[analyze] [pointer] [index %d] [addr %lx] [target %lx] [id %ld]\n", i, ptr->addr, ptr->target, ptr->access_id);
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
            // Type inference (Stage 4): pointer-typed objects get the
            // null/valid/oob candidate treatment via the decoded model.
            const OspreyDecodedObject *pobj = NULL;
            if (g_osprey_ctx != NULL) {
                const OspreyModel *pm = osprey_model(g_osprey_ctx);
                if (pm != NULL) {
                    pobj = osprey_lookup_raw(pm, (uint64_t)ptr->addr);
                }
            }
            if (pobj != NULL && pobj->kind == OSPREY_DECODED_POINTER) {
                log_msg("[inferred] [pointer] [addr %lx] [target %lx]\n",
                        ptr->addr, ptr->target);
                add_pointer_typed_candidate(mod_manager->modifications,
                                            &mod, pobj);
            } else {
                /* Not model-typed: keep the generic null/valid variants. */
                if (mod.value_addr == 0) {
                    memset(mod.value, 0, sizeof(target_ulong));
                }
                Modification *modification = add_single_modification(&mod);
                g_queue_push_tail(mod_manager->modifications, modification);
            }
        }

        for (int i = 0; i < mod_primitive_candidates->len; i++) {
            MutationCandidate mod = g_array_index(mod_primitive_candidates, MutationCandidate, i);
            if (binradar_manager_check_addr(mod.addr)) {
                log_msg("[binradar] [skip-mod] [addr %lx]\n", mod.addr);
                continue;
            }
            add_modification_primitive(mod_manager->modifications, &mod);
        }
        log_msg("[analyze] [queue] [len %d]\n", g_queue_get_length(mod_manager->modifications));
        g_array_free(mod_primitive_candidates, true);
        return select_next_modification(exit_info);
    } else {
        /* Feedback loop not implemented; no new modifications
         * are generated on subsequent iterations. */
        g_array_free(mod_primitive_candidates, true);
    }
    return select_next_modification(exit_info);
}

static int binradar_manager_cur_patch_id(BinradarManager *manager, int new_patch_id) {
    if (manager == NULL) return -1;
    if (manager->current == NULL) return -1;
    if (new_patch_id >= 0) {
        *manager->cur_patch_id = new_patch_id;
    }
    return *manager->cur_patch_id;
}

static int binradar_manager_cur_iter(BinradarManager *manager, int new_iter) {
    if (manager == NULL) return -1;
    if (manager->current == NULL) return -1;
    if (new_iter >= 0) {
        *manager->cur_iter = new_iter;
    }
    return *manager->cur_iter;
}

static int binradar_manager_get_patch_cnt(BinradarManager *manager) {
    if (manager == NULL) return 0;
    if (manager->current == NULL) return 0;
    return manager->patch_cnt;
}

// Actual patch id for iteration index (0 = original program, then candidates)
static int binradar_manager_patch_id_at(BinradarManager *manager, uint32_t index) {
    if (manager == NULL) return 0;
    if (index == 0) return 0;
    if (index > manager->patch_cnt) return 0;
    if (manager->patch_list == NULL) return (int)index;
    return (int)manager->patch_list[index - 1];
}

static void binradar_commit(BinradarManager *manager) {
    // Clone current patched result and add to results
    if (manager == NULL) return;
    if (manager->current == NULL) return;
    int cur_iter = binradar_manager_cur_iter(manager, -1);
    if (cur_iter < 1) return;
    BinradarResult *clone = binradar_manager_alloc_one_iter(manager);
    clone->iter = cur_iter;
    char br_buf[4096];
    memset(br_buf, 0, sizeof(br_buf));
    for (uint32_t i = 0; i < manager->patch_cnt + 1; i++) {
        int patch = binradar_manager_patch_id_at(manager, i);
        PatchedResult res = manager->current->patch_results[patch];
        if (res.br_taken == NULL) {
            log_msg("[binradar] [commit] [iter %d] [patch %d] [br null]\n", cur_iter, patch);
            clone->patch_results[patch] = res;
            continue;
        }
        size_t n = res.br_taken->len;
        if (n >= sizeof(br_buf)) {
            n = sizeof(br_buf) - 1;
        }
        for (size_t j = 0; j < n; j++) {
            int taken = g_array_index(res.br_taken, int, j);
            br_buf[j] = taken == 2 ? '2' : (taken ? '1' : '0');
        }
        br_buf[n] = '\0';
        log_msg("[binradar] [commit] [iter %d] [patch %d] [br %s]\n", cur_iter, patch, br_buf);
        clone->patch_results[patch] = res;
        if (cur_iter == 1) {
            break;
        }
    }
    memset(manager->current->patch_results, 0, sizeof(PatchedResult) * (manager->patch_max_id + 1));
    g_ptr_array_add(manager->results, clone);
}

static void set_nonblock(int fd) {
    int flags = fcntl(fd, F_GETFL);
    if (flags < 0) {
        log_msg("fcntl(F_GETFL)");
        exit_with_status(1);
    }
    if (fcntl(fd, F_SETFL, flags | O_NONBLOCK) < 0) {
        log_msg("fcntl(F_SETFL)");
        exit_with_status(1);
    }
}

static PatchedResult *get_patched_result_tmp(BinradarManager *manager, uint32_t patch_id) {
    if (manager == NULL) {
        log_msg("Manager not initialized");
        exit_with_status(1);
    }
    if (manager->current == NULL) {
        log_msg("Current result not initialized");
        exit_with_status(1);
    }
    if (patch_id > manager->patch_max_id) {
        log_msg("Invalid patch ID: %u", patch_id);
        exit_with_status(1);
    }
    return &manager->current->patch_results[patch_id];
}

static void binradar_manager_handle_patch_line(BinradarManager *manager, const char *line) {
    sbsv_row *row = NULL;
    log_msg("[binradar] [patch-res] %s\n", line);
    sbsv_parser_parse_line_detached(manager->patch_result_parser, line, 0, &row);
    int cur_iter = binradar_manager_cur_iter(manager, -1);
    if (row != NULL) {
        if (strcmp(sbsv_row_schema_name(row), "patch") == 0) {
            // Process patch row
            long long patch_id = sbsv_row_get_int(row, "id", NULL);
            long long br = sbsv_row_get_int(row, "br", NULL);
            long long iter = sbsv_row_get_int(row, "v", NULL);
            if (iter != cur_iter) {
                log_msg("[binradar] [iter-mismatch] [v %lld] [iter %d] [id %lld] [br %lld]\n", iter, cur_iter, patch_id, br);
                sbsv_row_free(row);
                return;
            }
            if (patch_id < 0 || patch_id > UINT32_MAX) {
                log_msg("[binradar] [invalid-patch-id] [id %lld]\n", patch_id);
                sbsv_row_free(row);
                return;
            }
            PatchedResult *result = get_patched_result_tmp(manager, patch_id);
            if (result->br_taken == NULL) {
                result->br_taken = g_array_new(FALSE, FALSE, sizeof(int));
            }
            int br_taken = (int)br;
            g_array_append_val(result->br_taken, br_taken);
        }
        sbsv_row_free(row);
    }
}

static void binradar_manager_handle_patch_bytes(BinradarManager *manager, const char *buf, size_t len) {
    for (size_t i = 0; i < len; i++) {
        char c = buf[i];

        if (manager->line_idx + 1 >= sizeof(manager->line_buf)) {
            // Line too long, reset buffer
            manager->line_buf[manager->line_idx] = '\0';
            binradar_manager_handle_patch_line(manager, manager->line_buf);
            manager->line_idx = 0;
        }

        manager->line_buf[manager->line_idx++] = c;

        if (c == '\n') {
            manager->line_buf[manager->line_idx - 1] = '\0';
            binradar_manager_handle_patch_line(manager, manager->line_buf);
            manager->line_idx = 0;
        }
    }
}

static void binradar_manager_drain_patch_fd_once(BinradarManager *manager) {
    char buf[4096];
    for (;;) {
        ssize_t n = read(manager->patch_fd_r, buf, sizeof(buf));
        if (n > 0) {
            binradar_manager_handle_patch_bytes(manager, buf, (size_t)n);
            continue;
        }
        if (n == 0) {
            // write end closed
            break;
        }
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
            break;
        }
        if (errno == EINTR) {
            continue;
        }
        break;
    }
}

static void binradar_manager_reset_line_buf(BinradarManager *manager) {
    if (manager == NULL) return;
    manager->line_idx = 0;
    memset(manager->line_buf, 0, sizeof(manager->line_buf));
}

static int64_t forkserver_child_timeout_ms(void) {
    const char *var = getenv("BINRADAR_FORKSERVER_CHILD_TIMEOUT");
    if (var == NULL) return -1;
    int64_t secs = atoll(var);
    if (secs <= 0) return -1;
    return secs * 1000;
}

/* Parent-side deferred-finding reporter: after the child died (or was
 * killed on timeout), surface any provenance finding the child recorded
 * in shared memory.  Returns true if a finding was reported. */
static bool report_shared_prov_finding(uint32_t *status_out) {
    if (shared_trace_data == NULL) return false;
    /* Acquire-load the shared publication state and copy the whole
     * record once, so a promotion cannot be observed half-written. */
    ProvPublishedFinding fault;
    if (!provenance_snapshot_pending_finding(&fault)) {
        return false;
    }
    ProvFindingRecord *f = &fault.payload;
    /* Emit the structured finding exactly once (dual-record policy). */
    provenance_report_pending_finding();
    /* Synthetic crash verdict (SIGSEGV) so the outer harness sees a crash
     * rather than a pure timeout. */
    if (status_out != NULL) {
        *status_out = 128 + SIGSEGV;
    }
    /* Publish the exit record with the child's final solver cursors
     * (shared pools are attached at the same addresses before fork, so
     * the child's cursor indices are valid in the parent).  The child was
     * killed before guest-exit finalization, so this is the only exit
     * publication for the timeout path. */
    SnapshotExitInfo *info = snapshot_exit_info_ptr();
    if (info != NULL && !info->valid) {
        memset(info, 0, sizeof(*info));
        info->valid = 1;
        info->crashed = 1;
        info->target_signal = TARGET_SIGSEGV;
        info->host_signal = 0;
        info->si_code = SEGV_ACCERR;
        info->exit_code = 139;
        info->guest_pc = f->access_pc;
        info->guest_cs_base = 0;
        info->fault_addr = f->access_pc;
        info->host_fault_addr = 0;
        info->guest_last_translation_block = last_translation_block;
        info->next_query = (fault.finding_query_idx >= 0 && query_queue)
            ? query_queue + fault.finding_query_idx : next_query;
        info->next_free_expr = (fault.finding_expr_idx >= 0 && pool)
            ? pool + fault.finding_expr_idx : next_free_expr;
        const char *pf_reason = provenance_fault_reason();
        g_strlcpy(info->description,
                  pf_reason ? pf_reason : "memcheck: provenance finding",
                  SNAPSHOT_EXIT_DESC_LEN);
        log_msg("[snapshot] [exit] [crash] [entrypoint-hit %lu]\n",
                binradar_entrypoint_hit_count);
        snapshot_log_cursor_indices(info);
        log_msg("[snapshot] [crash] [hit-count %lu] [reason %s] [guest_pc %lx] [guest_cs_base %lx] [fault_addr %lx] [host_fault_addr %lx]\n",
                binradar_entrypoint_hit_count,
                info->description, info->guest_pc, info->guest_cs_base,
                info->fault_addr, info->host_fault_addr);
    }
    return true;
}

static int wait_child_and_drain_patch(pid_t child_pid, uint32_t *status_out) {
        if (binradar_manager == NULL) {
        // Not binradar mode - fallback to original
        int64_t timeout_ms = forkserver_child_timeout_ms();
        if (timeout_ms < 0) {
            return waitpid(child_pid, (int *)status_out, 0);
        }
        // Bounded wait with deadline
        int status = 0;
        int64_t deadline = g_get_monotonic_time() + timeout_ms * 1000; /* us */
        for (;;) {
            pid_t r = waitpid(child_pid, &status, WNOHANG);
            if (r == child_pid) {
                *status_out = (uint32_t)status;
                /* Child exited on its own; a deferred finding is already
                 * surfaced by the child's finalize path. */
                return 0;
            }
            if (r < 0) {
                log_msg("waitpid(WNOHANG)\n");
                return -1;
            }
            if (g_get_monotonic_time() >= deadline) {
                log_msg("[forkserver] [child-timeout] killing child %d after %ld ms\n",
                        (int)child_pid, (long)timeout_ms);
                kill(child_pid, SIGKILL);
                waitpid(child_pid, &status, 0);
                *status_out = (uint32_t)status;
                /* Timeout-safe transport: the child may have recorded a
                 * provenance finding before looping forever.  Surface it
                 * as a synthetic crash instead of a bare timeout. */
                report_shared_prov_finding(status_out);
                return 0;
            }
            g_usleep(50 * 1000);
        }
    }

    struct pollfd pfd;
    int status = 0;
    bool child_exited = false;

    memset(&pfd, 0, sizeof(pfd));
    pfd.fd = binradar_manager->patch_fd_r;
    pfd.events = POLLIN | POLLHUP | POLLERR;

    if (binradar_manager->patch_fd_r > 0) {
        set_nonblock(binradar_manager->patch_fd_r);
    }

    int64_t timeout_ms = forkserver_child_timeout_ms();
    int64_t deadline = (timeout_ms >= 0) ? g_get_monotonic_time() + timeout_ms * 1000 : -1; /* us */

    while (!child_exited) {
        if (deadline >= 0 && g_get_monotonic_time() >= deadline) {
            log_msg("[forkserver] [child-timeout] killing child %d after %ld ms\n",
                    (int)child_pid, (long)timeout_ms);
            kill(child_pid, SIGKILL);
            waitpid(child_pid, &status, 0);
            child_exited = true;
            /* Timeout-safe transport: surface a deferred finding as a
             * synthetic crash (see non-binradar path above). */
            report_shared_prov_finding((uint32_t *)&status);
            break;
        }

        pid_t r = waitpid(child_pid, &status, WNOHANG);
        if (r == child_pid) {
            child_exited = true;
            break;
        } else if (r < 0) {
            log_msg("waitpid(WNOHANG)\n");
            return -1;
        }

        int pr = poll(&pfd, 1, 50);
        if (pr < 0) {
            if (errno == EINTR) {
                continue;
            }
            log_msg("poll\n");
            return -1;
        }

        if (pr == 0) {
            continue;
        }

        if (pfd.revents & (POLLIN | POLLHUP)) {
            binradar_manager_drain_patch_fd_once(binradar_manager);
        }

        if (pfd.revents & POLLERR) {
            log_msg("patch pipe POLLERR\n");
            binradar_manager_drain_patch_fd_once(binradar_manager);
        }
    }

    binradar_manager_drain_patch_fd_once(binradar_manager);

    *status_out = (uint32_t)status;
    return 0;
}


void snapshot_forkserver(CPUState *cpu, CPUArchState *cpu_env, const ArgumentInfo *arg_info, size_t num_arg_regs) {
    log_msg("[snapshot] [forkserver] [called %d]\n", forkserver_installed);
    if (forkserver_installed) return;
    forkserver_installed = true;
    rcu_disable_atfork();
    snapshot_save();
    if (binradar_forkserver_ctrl_r == -1 || binradar_forkserver_stat_w == -1) {
        log_msg("[snapshot] [forkserver] [error] invalid binradar control fds\n");
        exit_with_status(1);
    }
    pid_t child_pid;
    // int   t_fd[2];
    int patch_cnt = 0;
    if (binradar_manager != NULL) {
        patch_cnt = binradar_manager_get_patch_cnt(binradar_manager);
        binradar_manager_reset_line_buf(binradar_manager);
    }
    int binradar_iter = 0;
    int binradar_patch_id = 0;
    bool binradar_mode = (binradar_manager != NULL);
    
    uint32_t   was_killed;
    uint32_t version = 0x41464c00;
    uint32_t tmp = version ^ 0xffffffff, reply_value;
    uint8_t *msg = (uint8_t *)&version;
    uint8_t *reply = (uint8_t *)&reply_value;
    uint32_t analyze_result_len = 0;
    uint32_t analyze_result_len_prev = 0;
    uint8_t *analyze_result = NULL;
    uint32_t status[3] = {0, 0, 0}; // status[0]: child exit status, status[1]: patch id, status[2]: iter
    uint32_t remaining_mods = 0;
    /* Tell the parent that we're alive. If the parent doesn't want
       to talk, assume that we're not running in forkserver mode. */
  
    if (write_exact(binradar_forkserver_stat_w, msg, 4) < 0) {
        log_msg("[snapshot] [forkserver] [error] failed to write to %d %d\n", binradar_forkserver_stat_w, status);
        exit_with_status(1);
    }
  
    afl_forksrv_pid = getpid();
  
    if (read_exact(binradar_forkserver_ctrl_r, reply, 4) < 0) {
        log_msg("[snapshot] [forkserver] [error] fuzzolic not responding to %d\n", binradar_forkserver_ctrl_r);
        exit_with_status(1);
    }
    if (tmp != reply_value) {
        log_msg("wrong forkserver message from fuzzolic.py");
        exit_with_status(1);
    }

    // send welcome message as final message
    if (write_exact(binradar_forkserver_stat_w, msg, 4) < 0) { 
        log_msg("[snapshot] [forkserver] [error] failed to send final handshake to %d %d\n", binradar_forkserver_stat_w, status);
        exit_with_status(1);
    }
  
  
    // END forkserver handshake
    log_msg("[forkserver] [start]\n");
  
    /* All right, let's await orders... */
  
    while (1) {
  
        /* Whoops, parent dead? */
    
        if (read_exact(binradar_forkserver_ctrl_r, &was_killed, 4) < 0) {
            log_msg("[forkserver] [exit] parent (fuzzolic) dead or exit\n");
            exit_with_status(2);
        }
        if (binradar_mode && binradar_iter == 0) {
            binradar_iter = 1;
            binradar_patch_id = 0;
        } else if (!binradar_mode) {
            binradar_iter++;
        }
        binradar_manager_cur_iter(binradar_manager, binradar_iter);

        /* Establish a channel with child to grab translation commands. We'll
        read from t_fd[0], child will write to TSL_FD. */

        // if (pipe(t_fd) || dup2(t_fd[1], TSL_FD) < 0) exit(3);
        // close(t_fd[1]);
        if (binradar_mode) {
            int actual_patch_id = binradar_manager_patch_id_at(binradar_manager, (uint32_t)binradar_patch_id);
            status[1] = actual_patch_id;
            status[2] = binradar_iter;
            binradar_manager_cur_patch_id(binradar_manager, actual_patch_id);
            log_msg("[binradar] [shm] [patch-id %d] [iter %d]\n", *binradar_manager->cur_patch_id, *binradar_manager->cur_iter);
        }
        fflush(NULL);
        trace_mem_flush();
        log_msg_flush();
        /* OSPREY: prepare the shared run for the next sample.  After
         * the snapshot freeze, this resets only the per-child suffix,
         * preserving the frozen pre-snapshot prefix (Stage 2.1); the
         * child inherits `prefix ∪ empty suffix` via fork. */
        if (g_osprey_ctx != NULL && g_osprey_shared_run != NULL) {
            osprey_shared_run_prepare(g_osprey_ctx, g_osprey_shared_run,
                                      (uint64_t)binradar_iter);
        }
        child_pid = fork();
        if (child_pid < 0) exit_with_status(4);

        if (!child_pid) {
#ifdef SNAPSHOT_DEBUG
            snapshot_install_crash_handler();
#endif
            /* Child process. Reset shared trace data, close descriptors, run target program. */
            snapshot_modify_memory(cpu_env);
            /* Fresh per-input run: no inherited deferred fault. */
            provenance_clear_pending_fault();
            /* OSPREY: child side attaches to the shared run (post-fork
             * re-registration in case the parent reset recreated it). */
            if (g_osprey_ctx != NULL && g_osprey_shared_run != NULL) {
                osprey_child_use_shared_run(g_osprey_ctx,
                                            g_osprey_shared_run);
            }
            afl_fork_child = 1;
            close(binradar_forkserver_ctrl_r);
            close(binradar_forkserver_stat_w);
            // close(t_fd[0]);
            return;

        }

        /* Parent. */

        // close(TSL_FD);


        /* Parent. */

        /* Collect translation requests until child dies and closes the pipe. */

        // afl_wait_tsl(cpu, t_fd[0]);

        /* Get and relay exit status to parent. */

        if (wait_child_and_drain_patch(child_pid, status) < 0) exit_with_status(6);

        // Child process exit
        trace_mem_flush();
        /* OSPREY: the child has finished writing; merge its sample into
         * the committed context tables (parent side).  Only the
         * unmodified baseline sample (patch 0, iteration 1) is merged;
         * later mutation runs are never merged.  A failed merge rejects
         * the analysis transaction (Stage 0). */
        if (g_osprey_ctx != NULL && g_osprey_shared_run != NULL &&
            g_osprey_ctx->config.enabled &&
            binradar_mode && binradar_iter == 1 && binradar_patch_id == 0) {
            OspreyStatus mst = osprey_parent_merge_sample(
                g_osprey_ctx, g_osprey_shared_run);
            if (mst != OSPREY_OK && mst != OSPREY_DISABLED) {
                /* The merge already rejected the transaction; do not
                 * run analysis on incomplete facts. */
                log_msg("[forkserver] [osprey] [merge-failed] [status %d]\n",
                        (int)mst);
            }
        }
        if (write_exact(binradar_forkserver_stat_w, status, sizeof(status)) < 0) exit_with_status(7);

        // Get type inference result
        if (read_exact(binradar_forkserver_ctrl_r, &analyze_result_len, 4) < 0) {
            log_msg("[forkserver] [error] failed to read analyze_result_len from %d\n", binradar_forkserver_ctrl_r);
            exit_with_status(8);
        }
        log_msg("[forkserver] [analyze-result] [len %lu]\n", analyze_result_len);

        if (analyze_result_len > 0) {
            if (analyze_result_len > analyze_result_len_prev) {
                g_free(analyze_result);
                analyze_result = g_malloc(analyze_result_len + 1);
                analyze_result_len_prev = analyze_result_len;
            }
            if (read_exact(binradar_forkserver_ctrl_r, analyze_result, analyze_result_len) < 0) {
                log_msg("[forkserver] [error] failed to read analyze_result from %d\n", binradar_forkserver_ctrl_r);
                exit_with_status(9);
            }
            analyze_result[analyze_result_len] = '\0';
            log_msg("[forkserver] [analyze-result] [accept %lu]\n", analyze_result_len);
        }

        if (binradar_mode) {
            if (binradar_iter == 1) {
                /* OSPREY: baseline sample is merged; run the in-process
                 * analysis (closure/inference in Stages 2-4) only when
                 * the merge succeeded (fail-closed transaction). */
                if (g_osprey_ctx != NULL &&
                    g_osprey_ctx->config.enabled &&
                    osprey_tx_ok(g_osprey_ctx)) {
                    osprey_analyze(g_osprey_ctx);
                }
                remaining_mods = analyze_collected_data(arg_info, num_arg_regs);
                binradar_commit(binradar_manager);
                binradar_iter = 2;
                binradar_patch_id = 0;
            } else if (binradar_patch_id >= patch_cnt) {
                binradar_commit(binradar_manager);
                remaining_mods = analyze_collected_data(arg_info, num_arg_regs);
                binradar_iter++;
                binradar_patch_id = 0;
            } else {
                binradar_patch_id++;
            }
        }

        // Send remaining count
        if (write_exact(binradar_forkserver_stat_w, &remaining_mods, 4) < 0) exit_with_status(10);
  
    }

}

SnapshotMemRegion *mr_manager_heap_search_pub(target_ulong addr) { return mr_manager_heap_search(addr); }
