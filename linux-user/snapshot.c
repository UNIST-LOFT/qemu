#include "snapshot.h"
#include "provenance.h"
#include "sem-events.h"
#include "osprey.h"
#include "osprey-internal.h"
#include "snapshot-mutation.h"
#include "snapshot-mutation-internal.h"
#include "snapshot-mutation-symbolic.h"
#include "snapshot-observation.h"
#include "snapshot-osprey-adapter.h"
#include "binradar-cache.h"
#include "binradar-forkserver.h"
#include "e9-ranges.h"
#include "../tcg/symbolic/symbolic-struct.h"
#include "sbsv.h"
#include "qemu/rcu.h"
#include "qapi/error.h"
#include "qapi/qmp/qdict.h"
#include "qapi/qmp/qjson.h"
#include "qapi/qmp/qlist.h"
#include "qapi/qmp/qnum.h"

#include <fcntl.h>
#include <poll.h>
#include <stdio.h>
#include <stdint.h>
#include <limits.h>

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
/* Exact E9 exclusion intervals (loader + RESERVE + TRAMPOLINE maps of the
 * executing artifact), parsed from E9_EXCLUDE_RANGES.  Missing or empty
 * means no E9 regions. */
static e9_exclude_region *binradar_exclude_regions = NULL;
static size_t binradar_exclude_regions_len = 0;
static size_t binradar_exclude_regions_cap = 0;

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


typedef struct ModificationManager {
    GQueue *modifications; // Queue<SnapshotMutationPlan *>
    SnapshotMutationPlan *current;
} ModificationManager;






static SharedTraceData *shared_trace_data = NULL;
/* OSPREY in-process structural type analysis (Stage 1: shared-run fact
 * transport).  The parent allocates one fixed-layout MAP_SHARED run and
 * resets it before each fork; the child attaches and the parent merges the
 * completed sample after waitpid. */
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
/* Separate lifetime state from the owned manager pointer: after the queue is
 * exhausted the manager is destroyed, but analysis must not restart and trace
 * collection must stay disabled. */
static bool mutation_analysis_started = false;
static uint64_t next_snapshot_mutation_epoch = 0;
static int64_t snapshot_mutation_query_start = -1;
static int64_t snapshot_mutation_expr_start = -1;
static SnapshotMutationBaseline *snapshot_mutation_baseline = NULL;
static SnapshotExitInfo original_exit_info;

static BinradarManager *binradar_manager = NULL;

static void trace_mem_flush(void);
static void snapshot_modification_manager_reset(bool analysis_started);
static void exit_with_status(int status);
bool is_e9_relocated_call(target_ulong pc, target_ulong *call_site,
                          target_ulong *ret_addr);

/* Parse E9_EXCLUDE_RANGES: a canonical comma-separated list of half-open
 * intervals.  Missing or empty initializes an empty collection.  A
 * malformed non-empty value is a configuration error: emit one structured
 * diagnostic and terminate before guest execution rather than continue
 * with a partial list.  The getenv() storage is never modified. */
void parse_e9_exclude_ranges(uintptr_t load_bias) {
    const char *value = getenv("E9_EXCLUDE_RANGES");
    if (value == NULL || value[0] == '\0') {
        return;
    }
    size_t len = 0;
    size_t cap = 0;
    if (e9_parse_exclude_ranges(value, load_bias, &binradar_exclude_regions,
                                &len, &cap) != 0) {
        log_msg("[snapshot] [parse-e9-exclude-range] [invalid-format] "
                "[value %s]\n", value);
        exit_with_status(1);
    }
    binradar_exclude_regions_len = len;
    binradar_exclude_regions_cap = cap;
    for (size_t i = 0; i < len; i++) {
        log_msg("[snapshot] [parse-e9-exclude-range] [start %lx] [end %lx]\n",
                (unsigned long)binradar_exclude_regions[i].start,
                (unsigned long)binradar_exclude_regions[i].end);
    }
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
    check_env_var("BINRADAR_FORKSERVER_ITERATION_TIMEOUT");
    // Memcheck related
    check_env_var("BINRADAR_MEMCHECK_ENABLE");
    // Patch related
    check_env_var("BINRADAR_PATCH_FD_R");
    check_env_var("PATCH_FD"); // Used by brpatch
    check_env_var("PATCH_ID"); // Used by brpatch, 123456
    check_env_var("BINRADAR_PATCH_CNT");
    check_env_var("BINRADAR_PATCH_FILTER_FILE");
    check_env_var("BINRADAR_EVIDENCE_FILE");
    check_env_var("BINRADAR_PATCH_CACHE_ENABLE");
    check_env_var("BINRADAR_PATCH_MANIFEST");
    check_env_var("BINRADAR_PATCH_CACHED_FD_R");
    check_env_var("PATCH_CACHED_FD");
    // e9tool patch region related
    check_env_var("E9_EXCLUDE_RANGES");
    // E9Patch relocated call jumps (jump-addr:call-site:ret-addr, comma separated)
    check_env_var("E9_RELOCATED_CALL_JUMPS");
    // Symbolic transport
    check_env_var("NO_EXTERNAL_SOLVER");
    // Shared memory
    check_env_var("EXPR_POOL_SHM_KEY");
    check_env_var("QUERY_SHM_KEY");
    check_env_var("BITMAP_SHM_KEY");
    check_env_var("BINRADAR_PATCH_SHM_KEY");
    // Symbolic boundary advisor (BinRadar only)
    check_env_var("BINRADAR_SYMBOLIC_MUTATION_MODE");
    check_env_var("BINRADAR_SYMBOLIC_MAX_WORK");
    check_env_var("BINRADAR_SYMBOLIC_MAX_BYTES");
    check_env_var("BINRADAR_SYMBOLIC_DEADLINE_MS");
    check_env_var("BINRADAR_SYMBOLIC_TEST_DETAIL");
}

void add_exclude_regions(uintptr_t load_bias) {
    parse_e9_exclude_ranges(load_bias);
}

bool is_in_e9_exclude_region(target_ulong pc) {
    return e9_is_in_exclude_region(binradar_exclude_regions,
                                   binradar_exclude_regions_len, pc);
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
    snapshot_modification_manager_reset(false);
    exit(status);
}

void snapshot_init_binradar_patch_shm(uintptr_t key) {
    const char *var;
    size_t shm_size = sizeof(uint32_t) * 2u;
    binradar_manager = g_new0(BinradarManager, 1);
    binradar_manager->patch_cnt = 1;
    binradar_manager->patch_fd_r = -1;
    binradar_manager->cache_fd_r = -1;

    var = getenv("BINRADAR_PATCH_CNT");
    if (var == NULL || atoi(var) < 0) {
        log_msg("BINRADAR_PATCH_CNT not set or invalid\n");
        exit_with_status(1);
    }
    binradar_manager->patch_cnt = (uint32_t)atoi(var);
    binradar_manager->patch_max_id = binradar_manager->patch_cnt;
    var = getenv("BINRADAR_PATCH_FILTER_FILE");
    if (var != NULL && var[0] != '\0' &&
        !binradar_cache_load_filter(binradar_manager, var)) {
        exit_with_status(1);
    }

    var = getenv("BINRADAR_EVIDENCE_FILE");
    if (var == NULL || var[0] == '\0') {
        log_msg("[binradar] [evidence] [error missing-path]\n");
        exit_with_status(1);
    }
    binradar_manager->evidence_file = fopen(var, "wb");
    if (binradar_manager->evidence_file == NULL ||
        !br_evidence_write_header(binradar_manager->evidence_file,
                                  BR_EVIDENCE_KIND_BINRADAR) ||
        fflush(binradar_manager->evidence_file) != 0) {
        log_msg("[binradar] [evidence] [error open] [file %s]\n", var);
        exit_with_status(1);
    }
    log_msg("[binradar] [evidence] [file %s] [version 1]\n", var);

    var = getenv("BINRADAR_PATCH_CACHE_ENABLE");
    binradar_manager->cache_enabled = var != NULL && strcmp(var, "1") == 0;
    binradar_manager->cache_inference_enabled =
        binradar_manager->cache_enabled;
    if (binradar_manager->cache_enabled) {
        const char *manifest = getenv("BINRADAR_PATCH_MANIFEST");
        const char *cache_fd = getenv("BINRADAR_PATCH_CACHED_FD_R");
        if (manifest == NULL || manifest[0] == '\0' || cache_fd == NULL ||
            atoi(cache_fd) <= 2 ||
            !binradar_cache_load_manifest(binradar_manager, manifest)) {
            log_msg("[binradar] [cache-manifest] [fatal configuration]\n");
            exit_with_status(1);
        }
        binradar_manager->cache_fd_r = atoi(cache_fd);
        if (binradar_manager->cache_family == BRCACHE_FAMILY_CWE805) {
            uint64_t required = 0;
            for (uint32_t i = 0; i < binradar_manager->patch_cnt; i++) {
                uint32_t id = binradar_manager->patch_list != NULL
                    ? binradar_manager->patch_list[i] : i + 1u;
                BinradarCachePredicate *predicate =
                    &binradar_manager->cache_predicates[id];
                uint64_t width;
                switch (predicate->cell_kind) {
                case BRCACHE_CELL_REGISTER: width = 0; break;
                case BRCACHE_CELL_STACK8: width = 1; break;
                case BRCACHE_CELL_STACK16: width = 2; break;
                case BRCACHE_CELL_STACK32: width = 4; break;
                case BRCACHE_CELL_STACK64: width = 8; break;
                default: width = UINT64_MAX; break;
                }
                uint64_t bytes = width == UINT64_MAX ? UINT64_MAX :
                    (width == 0 ? 0 :
                     ((uint64_t)predicate->cell_index + 1u) * width);
                required = MAX(required, bytes);
            }
            const char *stack_size = getenv("BRCACHE_STACK_SIZE");
            char *end = NULL;
            errno = 0;
            uint64_t parsed = stack_size != NULL
                ? strtoull(stack_size, &end, 0) : 0;
            if (stack_size == NULL || stack_size[0] == '\0' || errno != 0 ||
                end == stack_size || *end != '\0' || parsed < required ||
                parsed > (1u << 20)) {
                log_msg("[binradar] [cache-manifest] "
                        "[error invalid-stack-size] [required %" PRIu64 "]\n",
                        required);
                exit_with_status(1);
            }
            binradar_manager->cache_stack_size = (uint32_t)parsed;
        }
        shm_size = binradar_manager->selector_size;
        binradar_manager->cache_bytes = g_byte_array_new();
    }

    const char *feedback_dir = getenv("BINRADAR_FEEDBACK_DIR");
    if (feedback_dir != NULL && feedback_dir[0] != '\0') {
        if (!binradar_manager->cache_enabled) {
            log_msg("[binradar] [feedback] [disabled] "
                    "[reason brcached-required]\n");
        } else {
            const char *valid_text = getenv("BINRADAR_POC_FAULT_VALID");
            const char *source_text = getenv("BINRADAR_POC_FAULT_SOURCE");
            const char *fault_text = getenv("BINRADAR_POC_FAULT_ADDR");
            char *end = NULL;
            unsigned long long fault = 0;
            bool valid;
            SnapshotFaultReferenceSource source =
                SNAPSHOT_FAULT_REFERENCE_UNAVAILABLE;

            if (valid_text == NULL ||
                (strcmp(valid_text, "0") != 0 && strcmp(valid_text, "1") != 0) ||
                source_text == NULL ||
                !g_file_test(feedback_dir, G_FILE_TEST_IS_DIR)) {
                log_msg("[binradar] [feedback] [error configuration]\n");
                exit_with_status(1);
            }
            valid = strcmp(valid_text, "1") == 0;
            if (strcmp(source_text, "guest-signal") == 0) {
                source = SNAPSHOT_FAULT_REFERENCE_GUEST_SIGNAL;
            } else if (strcmp(source_text, "provenance-access") == 0) {
                source = SNAPSHOT_FAULT_REFERENCE_PROVENANCE_ACCESS;
            } else if (strcmp(source_text, "unavailable") != 0) {
                log_msg("[binradar] [feedback] [error configuration]\n");
                exit_with_status(1);
            }
            if (valid != (source != SNAPSHOT_FAULT_REFERENCE_UNAVAILABLE)) {
                log_msg("[binradar] [feedback] [error configuration]\n");
                exit_with_status(1);
            }
            if (valid) {
                errno = 0;
                fault = strtoull(fault_text != NULL ? fault_text : "",
                                 &end, 0);
                if (fault_text == NULL || fault_text[0] == '\0' ||
                    errno != 0 || end == fault_text || *end != '\0' ||
                    (target_ulong)fault != fault) {
                    log_msg("[binradar] [feedback] [error configuration]\n");
                    exit_with_status(1);
                }
            }
            binradar_manager->feedback_dir = g_strdup(feedback_dir);
            binradar_manager->poc_fault_valid = valid;
            binradar_manager->poc_fault_source = source;
            binradar_manager->poc_fault_addr = (target_ulong)fault;
            log_msg("[binradar] [feedback] [enabled] [dir %s] "
                    "[poc-fault-valid %s] [poc-fault-source %s] "
                    "[poc-fault-addr %lx]\n", feedback_dir,
                    valid ? "true" : "false",
                    snapshot_fault_reference_source_name(source),
                    binradar_manager->poc_fault_addr);
        }
    }

    int shmid = shmget((key_t)key, shm_size, 0666 | IPC_CREAT);
    if (shmid == -1) {
        perror("shmget failed");
        exit_with_status(1);
    }
    uint32_t *shm = shmat(shmid, NULL, 0);
    if (shm == (void *)-1) {
        perror("shmat failed");
        exit_with_status(1);
    }
    memset(shm, 0, shm_size);
    binradar_manager->cur_patch_id = shm;
    binradar_manager->cur_iter = shm + 1;
    if (binradar_manager->cache_enabled) {
        binradar_manager->selector = (BinradarPatchSelector *)shm;
        /* Iteration 0 is unpublished.  An E9 call may run before the guest
         * reaches BINRADAR_ENTRYPOINT and starts the forkserver; the cached
         * runtime must preserve original control flow until iteration 1. */
        binradar_manager->selector->patch_id = 0;
        binradar_manager->selector->iteration = 0;
        binradar_manager->selector->descriptor_length = 0;
        binradar_manager->selector->descriptor_capacity =
            (uint32_t)(shm_size - offsetof(BinradarPatchSelector,
                                           descriptor));
        binradar_manager->selector->descriptor[0] = '\0';
    }

    var = getenv("BINRADAR_PATCH_FD_R");
    if (var == NULL || atoi(var) <= 2) {
        log_msg("BINRADAR_PATCH_FD_R not set\n");
        exit_with_status(1);
    }
    binradar_manager->patch_fd_r = atoi(var);
    binradar_manager->current = binradar_cache_new_iteration(
        binradar_manager);
    binradar_manager->patch_result_parser = sbsv_parser_new(
        SBSV_PARSER_DEFAULT);
    sbsv_parser_add_schema(binradar_manager->patch_result_parser,
        "[patch] [id: int] [br: int] [v: int]");
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
    if (q == NULL || e == NULL) {
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
    if (mutation_analysis_started) {
        /* Analysis stays complete after the owned manager is destroyed. */
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
    info->query_cursor = (next_query != NULL && query_queue != NULL)
        ? (int64_t)(next_query - query_queue) : -1;
    info->expr_cursor = (next_free_expr != NULL && pool != NULL)
        ? (int64_t)(next_free_expr - pool) : -1;
}

static int64_t snapshot_query_cursor_index(const SnapshotExitInfo *info) {
    return info != NULL ? info->query_cursor : -1;
}

static int64_t snapshot_expr_cursor_index(const SnapshotExitInfo *info) {
    return info != NULL ? info->expr_cursor : -1;
}

/* Validate a child-published pool cursor once in the parent.  Cursors are raw
 * pointer differences into the shared pools, so they must be non-negative and
 * within the fixed capacity before any pointer is reconstructed from them. */
static bool snapshot_query_cursor_valid(int64_t cursor) {
    return cursor >= 0 && (uint64_t)cursor <= (uint64_t)EXPR_QUERY_CAPACITY;
}

static bool snapshot_expr_cursor_valid(int64_t cursor) {
    return cursor >= 0 && (uint64_t)cursor <= (uint64_t)EXPR_POOL_CAPACITY;
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

static void snapshot_emit_fault_reference(const SnapshotExitInfo *info)
{
    const char *source;
    bool valid;

    if (info == NULL) return;
    valid = info->fault_reference_valid != 0 &&
        (info->fault_reference_source ==
             SNAPSHOT_FAULT_REFERENCE_GUEST_SIGNAL ||
         info->fault_reference_source ==
             SNAPSHOT_FAULT_REFERENCE_PROVENANCE_ACCESS);
    source = valid ? snapshot_fault_reference_source_name(
        info->fault_reference_source) : "unavailable";
    log_msg("[snapshot] [fault-reference] [version 2] [valid %s] "
            "[source %s] [address %lx]\n",
            valid ? "true" : "false", source,
            valid ? info->fault_addr : 0ul);

    if (binradar_probe_file != NULL) {
        FILE *fp = fopen(binradar_probe_file, "a");
        if (fp == NULL) {
            fprintf(stderr, "Failed to open binradar probe file: %s\n",
                    binradar_probe_file);
        } else {
            fprintf(fp, "[snapshot] [fault-reference] [version 2] "
                    "[valid %s] [source %s] [address %lx]\n",
                    valid ? "true" : "false", source,
                    valid ? info->fault_addr : 0ul);
            fclose(fp);
        }
    }
}

static void snapshot_emit_crash_rows(const SnapshotExitInfo *info)
{
    if (info == NULL) return;
    snapshot_emit_fault_reference(info);
    log_msg("[snapshot] [exit] [crash] [entrypoint-hit %lu]\n",
             binradar_entrypoint_hit_count);
    snapshot_log_cursor_indices(info);
    log_msg("[snapshot] [crash] [hit-count %lu] [reason %s] "
            "[guest_pc %lx] [guest_cs_base %lx] [fault_addr %lx] "
            "[host_fault_addr %lx]\n",
            binradar_entrypoint_hit_count, info->description,
            info->guest_pc, info->guest_cs_base, info->fault_addr,
            info->host_fault_addr);
    if (binradar_manager) {
        int patch_id = binradar_cache_patch_id(binradar_manager, -1);
        int iter = binradar_cache_iteration(binradar_manager, -1);
        log_msg("[binradar] [crash] [iter %d] [patch %d] [guest_pc %lx] "
                "[guest_cs_base %lx] [fault_addr %lx] "
                "[host_fault_addr %lx] [reason %s]\n",
                iter, patch_id, info->guest_pc, info->guest_cs_base,
                info->fault_addr, info->host_fault_addr, info->description);
    }
    if (binradar_probe_file != NULL) {
        FILE *fp = fopen(binradar_probe_file, "a");
        if (fp == NULL) {
            fprintf(stderr, "Failed to open binradar probe file: %s\n",
                    binradar_probe_file);
        } else {
            fprintf(fp, "[snapshot] [crash] [hit-count %lu] [reason %s] "
                    "[guest_pc %lx] [guest_cs_base %lx] "
                    "[fault_addr %lx] [host_fault_addr %lx]\n",
                    binradar_entrypoint_hit_count, info->description,
                    info->guest_pc, info->guest_cs_base, info->fault_addr,
                    info->host_fault_addr);
            fclose(fp);
        }
    }
    dump_coverage_edge_log(true);
}

static void snapshot_record_guest_crash_with_reference(
    CPUArchState *cpu_env, int target_signal, int host_signal, int si_code,
    uintptr_t host_fault_addr, const char *reason,
    SnapshotFaultReferenceSource reference_source, target_ulong reference_addr)
{
    SnapshotExitInfo *info;

    snapshot_load_binradar_env();
    info = snapshot_exit_info_ptr();
    if (!snapshot_exit_info_should_update(info, true)) return;
    info->valid = 0;
    info->crashed = 1;
    info->target_signal = target_signal;
    info->host_signal = host_signal;
    info->si_code = si_code;
    info->exit_code = (host_signal > 0) ? (128 + host_signal) : -target_signal;
    info->host_fault_addr = host_fault_addr;
    snapshot_exit_info_capture(info, cpu_env);
    if (reference_source == SNAPSHOT_FAULT_REFERENCE_GUEST_SIGNAL) {
        reference_addr = info->guest_pc;
    }
    snapshot_exit_info_set_fault_reference(info, reference_source,
                                           reference_addr);
    char buffer[SNAPSHOT_EXIT_DESC_LEN];
    const char *base = reason ? reason : "unhandled signal";
    const char *host_name = (host_signal > 0) ? strsignal(host_signal) : NULL;
    if (host_name) {
        g_snprintf(buffer, sizeof(buffer), "%s (host=%s[%d], target=%d)",
                   base, host_name, host_signal, target_signal);
    } else {
        g_snprintf(buffer, sizeof(buffer), "%s (host=%d, target=%d)",
                   base, host_signal, target_signal);
    }
    snapshot_exit_info_set_reason(info, buffer);
    info->valid = 1;
    snapshot_emit_crash_rows(info);
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
        if (info != NULL && info->valid && info->crashed) {
            /* Real crash already recorded — the earlier record wins the
             * verdict; the finding was preserved above. */
            return;
        }
        snapshot_record_guest_crash_with_reference(
            cpu_env, TARGET_SIGSEGV, 0, SEGV_ACCERR, 0, pf_reason,
            SNAPSHOT_FAULT_REFERENCE_PROVENANCE_ACCESS,
            fault.payload.access_pc);
        return;
	}

    SnapshotExitInfo *info = snapshot_exit_info_ptr();
    if (!snapshot_exit_info_should_update(info, false)) return;
    info->valid = 0;
    info->crashed = 0;
    info->exit_code = exit_code;
    snapshot_exit_info_capture(info, cpu_env);
    snapshot_exit_info_set_fault_reference(
        info, SNAPSHOT_FAULT_REFERENCE_UNAVAILABLE, 0);
    snapshot_exit_info_set_reason(info, reason ? reason : "normal_exit");
    info->valid = 1;
	log_msg("[snapshot] [exit] [normal] [entrypoint-hit %lu]\n",
	        binradar_entrypoint_hit_count);
	snapshot_log_cursor_indices(info);
    if (binradar_manager) {
        int patch_id = binradar_cache_patch_id(binradar_manager, -1);
        int iter = binradar_cache_iteration(binradar_manager, -1);
        log_msg("[binradar] [normal] [iter %d] [patch %d] [guest_pc %lx] [guest_cs_base %lx] [reason %s]\n",
                  iter, patch_id, info->guest_pc, info->guest_cs_base, reason ? reason : "normal_exit");
    }
    
    dump_coverage_edge_log(true);
}

void snapshot_record_guest_crash(CPUArchState *cpu_env, int target_signal,
                                 int host_signal, int si_code,
                                 target_ulong fault_addr,
                                 uintptr_t host_fault_addr,
                                 const char *reason)
{
    (void)fault_addr;
    snapshot_record_guest_crash_with_reference(
        cpu_env, target_signal, host_signal, si_code, host_fault_addr, reason,
        target_signal > 0 ? SNAPSHOT_FAULT_REFERENCE_GUEST_SIGNAL
                          : SNAPSHOT_FAULT_REFERENCE_UNAVAILABLE,
        0);
}

static bool reserve_read_access_index(uint32_t *counter, uint32_t capacity,
                                      uint32_t *index_out) {
    uint32_t current = __atomic_load_n(counter, __ATOMIC_RELAXED);
    for (;;) {
        if (current >= capacity) {
            return false;
        }
        uint32_t next = current + 1;
        if (__atomic_compare_exchange_n(counter, &current, next, false,
                                        __ATOMIC_RELAXED,
                                        __ATOMIC_RELAXED)) {
            *index_out = current;
            return true;
        }
    }
}

static void remove_read_access_primitive(uintptr_t addr) {
    if (g_read_access_tainted_primitives == NULL) return;
    OrderedMapEntry *entry = ordered_map_lookup(g_read_access_tainted_primitives, addr);
    if (entry == NULL) return;
    // Remove from queue
    int idx_to_remove = entry->shared_index;
    g_queue_delete_link(g_read_access_tainted_primitives->queue, entry->node);
    uint32_t count = __atomic_load_n(&shared_trace_data->prim_idx,
                                     __ATOMIC_RELAXED);
    if (idx_to_remove < 0 || count == 0 ||
        count > MAX_PRIMITIVE_ACCESS || (uint32_t)idx_to_remove >= count) {
        /* Never underflow the published count or index the fixed array
         * from inconsistent ordered-map state. */
        shared_trace_data->prim_overflow = 1;
        trace_mem("[rpi] ERROR! remove primitive failed! idx %d count %u\n",
                  idx_to_remove, count);
        g_hash_table_remove(g_read_access_tainted_primitives->table,
                            GSIZE_TO_POINTER(addr));
        return;
    }
    uint32_t last_idx = count - 1;
    __atomic_store_n(&shared_trace_data->prim_idx, last_idx,
                     __ATOMIC_RELAXED);
    if ((uint32_t)idx_to_remove < last_idx) {
        PrimitiveAccess *src = &shared_trace_data->primitives[last_idx];
        PrimitiveAccess *dst = &shared_trace_data->primitives[idx_to_remove];
        *dst = *src;
        OrderedMapEntry *moved_entry = ordered_map_lookup(g_read_access_tainted_primitives, dst->addr);
        if (moved_entry != NULL) {
            moved_entry->shared_index = idx_to_remove;
            moved_entry->data = dst;
        }
        memset(src, 0, sizeof(PrimitiveAccess));
    } else {
        memset(&shared_trace_data->primitives[idx_to_remove], 0,
               sizeof(PrimitiveAccess));
    }
    g_hash_table_remove(g_read_access_tainted_primitives->table, GSIZE_TO_POINTER(addr));
}

static SnapshotReadToken add_read_access_pointer(CPUArchState *env,
                                                 uintptr_t addr,
                                                 uintptr_t target,
                                                 uintptr_t pc,
                                                 const uint8_t *observed,
                                                 uint32_t observed_size) {
    SnapshotReadToken token = {0};
    if (shared_trace_data == NULL) return token;
    if (g_read_access_pointers == NULL) g_read_access_pointers = ordered_map_init(MAX_POINTER_ACCESS);
    OrderedMapEntry *entry = ordered_map_insert(g_read_access_pointers, addr, NULL);
    PointerAccess *ptr = NULL;
    if (entry->shared_index < 0) {
        uint32_t new_index;
        if (reserve_read_access_index(&shared_trace_data->ptr_idx,
                                      MAX_POINTER_ACCESS, &new_index)) {
            entry->shared_index = (int)new_index;
            ptr = &shared_trace_data->pointers[new_index];
        }
    } else if (entry->shared_index < MAX_POINTER_ACCESS) {
        ptr = &shared_trace_data->pointers[entry->shared_index];
    }
    if (ptr == NULL) {
        /* Sticky: typed consumption must not run on an over-cap record
         * set.  The generic mutation path still exits with the previous
         * behavior. */
        shared_trace_data->ptr_overflow = 1;
        trace_mem("[rpo] ptr shared_index error!!! %d\n", entry->shared_index);
        exit_with_status(1);
    }
    ptr->addr = addr;
    ptr->target = target;
    ptr->pc = pc;
    ptr->access_id = __atomic_fetch_add(&shared_trace_data->ptr_access_cnt, 1, __ATOMIC_RELAXED);
    ptr->run_epoch = shared_trace_data->run_epoch;
    ptr->expr = NULL;
    /* A replaced record never carries symbolic metadata from the
     * previous occupant: the event token that named it is invalid. */
    memset(ptr->observed_read_bytes, 0, sizeof(ptr->observed_read_bytes));
    ptr->observed_read_valid = 0;
    ptr->root_extension = SNAPSHOT_MUTATION_ROOT_IDENTITY;
    ptr->expr_index = -1;
    ptr->query_index = -1;
    /* The successful child load supplies the physical bytes.  They are copied
     * here, at record-write time, so a later finalization cannot be confused
     * by a rewritten cell. */
    if (observed != NULL && observed_size >= 1 &&
        observed_size <= sizeof(ptr->observed_read_bytes)) {
        memcpy(ptr->observed_read_bytes, observed, observed_size);
        ptr->observed_read_valid = 1;
    }
    /* Stage 7.1: refresh locators on every write so a replaced record
     * never carries a stale identity.  Capture failure leaves the
     * locator zeroed (valid == 0); the record stays generic-eligible. */
    memset(&ptr->cell, 0, sizeof(ptr->cell));
    memset(&ptr->target_ref, 0, sizeof(ptr->target_ref));
    if (osprey_collect_enabled && g_osprey_ctx != NULL) {
        osprey_capture_chunk_ref(env, (target_ulong)addr,
                                 (target_ulong)sizeof(target_ulong),
                                 &ptr->cell);
        if (target != 0) {
            osprey_capture_address_ref(env, (target_ulong)target,
                                       &ptr->target_ref);
        }
    }
    entry->data = ptr;
    trace_mem("[rpo] [addr %lx] [target %lx] [pc %lx] [index %d] [id %ld]\n",
              addr, target, pc, entry->shared_index, ptr->access_id);
    token.run_epoch = ptr->run_epoch;
    token.access_id = ptr->access_id;
    token.slot = (uint32_t)entry->shared_index;
    token.lane = SNAPSHOT_READ_LANE_POINTER;
    token.valid = 1;
    return token;
}

static SnapshotReadToken add_read_access_primitive(CPUArchState *env,
                                                   uintptr_t addr,
                                                   int size, uintptr_t pc,
                                                   const uint8_t *observed,
                                                   uint32_t observed_size) {
    SnapshotReadToken token = {0};
    if (shared_trace_data == NULL) return token;
    if (g_read_access_pointers) {
        uintptr_t aligned_addr = addr & ~(uintptr_t)0x07;
        OrderedMapEntry *ptr_entry = ordered_map_lookup(g_read_access_pointers, aligned_addr);
        if (ptr_entry != NULL) {
            remove_read_access_primitive(addr);
            return token;
        }
    }
    if (g_read_access_tainted_primitives == NULL) g_read_access_tainted_primitives = ordered_map_init(MAX_PRIMITIVE_ACCESS);
    PrimitiveAccess *prim = NULL;
    OrderedMapEntry *entry = ordered_map_insert(g_read_access_tainted_primitives, addr, NULL);
    if (entry->shared_index < 0) {
        uint32_t new_index;
        if (reserve_read_access_index(&shared_trace_data->prim_idx,
                                      MAX_PRIMITIVE_ACCESS, &new_index)) {
            entry->shared_index = (int)new_index;
            prim = &shared_trace_data->primitives[new_index];
        }
    } else if (entry->shared_index < MAX_PRIMITIVE_ACCESS) {
        prim = &shared_trace_data->primitives[entry->shared_index];
    }
    if (prim == NULL) {
        /* Sticky: see add_read_access_pointer. */
        shared_trace_data->prim_overflow = 1;
        trace_mem("[rpo] prim shared_index error!!! %d\n", entry->shared_index);
        exit_with_status(1);
    }
    prim->addr = addr;
    prim->size = size;
    prim->pc = pc;
    prim->access_id = __atomic_fetch_add(&shared_trace_data->prim_access_cnt, 1, __ATOMIC_RELAXED);
    prim->run_epoch = shared_trace_data->run_epoch;
    prim->expr = NULL;
    /* See add_read_access_pointer: a replaced record carries no symbolic
     * metadata, so a token captured from the previous occupant cannot be
     * finalized against it. */
    memset(prim->observed_read_bytes, 0, sizeof(prim->observed_read_bytes));
    prim->observed_read_valid = 0;
    prim->root_extension = SNAPSHOT_MUTATION_ROOT_IDENTITY;
    prim->expr_index = -1;
    prim->query_index = -1;
    /* See add_read_access_pointer: the successful child load supplies the
     * physical bytes at record-write time. */
    if (observed != NULL && observed_size >= 1 &&
        observed_size <= sizeof(prim->observed_read_bytes)) {
        memcpy(prim->observed_read_bytes, observed, observed_size);
        prim->observed_read_valid = 1;
    }
    /* Stage 7.1: refresh the cell locator (see add_read_access_pointer). */
    memset(&prim->cell, 0, sizeof(prim->cell));
    if (osprey_collect_enabled && g_osprey_ctx != NULL) {
        osprey_capture_chunk_ref(env, (target_ulong)addr,
                                 (target_ulong)size, &prim->cell);
    }
    entry->data = prim;
    trace_mem("[rpi] [addr %lx] [size %d] [pc %lx] [index %d] [id %ld]\n",
              addr, size, pc, entry->shared_index, prim->access_id);
    token.run_epoch = prim->run_epoch;
    token.access_id = prim->access_id;
    token.slot = (uint32_t)entry->shared_index;
    token.lane = SNAPSHOT_READ_LANE_PRIMITIVE;
    token.valid = 1;
    return token;
}

/* Finalize a retained read once the load's machine-width root expression and
 * the admitted BINRADAR_CONCRETIZATION query are both known.  Every field of
 * the token must still name the same record: a replacement, a lane change, an
 * LRU slot move, or a new run epoch makes the token stale and the caller
 * abstains.  The observed bytes stay as captured by the record writer. */
bool snapshot_finalize_read_token(SnapshotReadToken token,
                                  int64_t expr_index, int64_t query_index,
                                  SnapshotRootExtension root_extension) {
    if (!forkserver_installed || shared_trace_data == NULL || !token.valid ||
        expr_index < 0 || query_index < 0 ||
        (query_queue != NULL && next_query != NULL &&
         query_index >= (int64_t)(next_query - query_queue)) ||
        (root_extension != SNAPSHOT_ROOT_IDENTITY &&
         root_extension != SNAPSHOT_ROOT_ZEXT &&
         root_extension != SNAPSHOT_ROOT_SEXT)) {
        return false;
    }
    if (token.run_epoch != shared_trace_data->run_epoch) return false;

    if (token.lane == SNAPSHOT_READ_LANE_POINTER &&
        token.slot < MAX_POINTER_ACCESS) {
        PointerAccess *ptr = &shared_trace_data->pointers[token.slot];
        if (ptr->access_id == token.access_id &&
            ptr->run_epoch == token.run_epoch) {
            ptr->expr_index = expr_index;
            ptr->query_index = query_index;
            ptr->root_extension = (uint8_t)root_extension;
            return true;
        }
        return false;
    }
    if (token.lane == SNAPSHOT_READ_LANE_PRIMITIVE &&
        token.slot < MAX_PRIMITIVE_ACCESS) {
        PrimitiveAccess *prim = &shared_trace_data->primitives[token.slot];
        if (prim->access_id == token.access_id &&
            prim->run_epoch == token.run_epoch) {
            prim->expr_index = expr_index;
            prim->query_index = query_index;
            prim->root_extension = (uint8_t)root_extension;
            return true;
        }
    }
    return false;
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
    shared_trace_data = snapshot_observation_create_shared();
    if (shared_trace_data == NULL) {
        log_msg("mmap shared memory failed");
        exit_with_status(1);
    }
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
        } else {
            /* Keep forkserver startup and generic mutation fallback alive, but
             * make a rejected OSPREY configuration observable. */
            log_msg("[osprey] [config] [disabled] [reason parse-failure]\n");
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

SnapshotReadToken snapshot_read_access(CPUArchState *env, SnapshotMemAccess *mem_access) {
    SnapshotReadToken none = {0};
    if (!forkserver_installed) return none;
    uintptr_t addr = mem_access->addr;
    uintptr_t size = mem_access->size;
    /* The successful child load supplies the physical bytes.  A caller that
     * did not populate them (out-of-range or oversized access) leaves the
     * observation invalid rather than reporting stale target bytes. */
    const uint8_t *observed = NULL;
    uint32_t observed_size = 0;
    if (mem_access->observed_valid && size >= 1 &&
        size <= sizeof(mem_access->target)) {
        observed = mem_access->target;
        observed_size = (uint32_t)size;
    }
    if (size == sizeof(target_ulong)) {
        target_ulong target;
        memcpy(&target, mem_access->target, sizeof(target_ulong));
        if (is_valid_address(target, true)) {
            // Add to pointer
            SnapshotReadToken token = add_read_access_pointer(
                env, addr, target, mem_access->pc, observed, observed_size);
            trace_mem("[snapshot] [raccess] [pointer] [addr %lx] [target %lx] [pc %lx]\n", addr, target, mem_access->pc);
            return token;
        } else if (target == 0) {
            // It may be a null pointer
            SnapshotReadToken token = add_read_access_primitive(
                env, addr, size, mem_access->pc, observed, observed_size);
            trace_mem("[snapshot] [raccess] [null-pointer] [addr %lx] [pc %lx]\n", addr, mem_access->pc);
            return token; // Do not add it twice
        } else {
            trace_mem("[snapshot] [raccess] [primitive] [addr %lx] [value %lx] [pc %lx]\n", addr, target, mem_access->pc);
        }
    }
    if (mem_access->symbolic_value) {
        // Tainted value
        SnapshotReadToken token = add_read_access_primitive(
            env, addr, size, mem_access->pc, observed, observed_size);
        trace_mem("[snapshot] [raccess] [mem] [addr %lx] [size %ld]\n", addr, size);
        return token;
    }
    trace_mem("[snapshot] [raccess] [mem] [addr %lx] [size %ld]\n", addr, size);
    return none;
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
                .observed_valid = false,
                .addr = syscall_arg1,
                .pc = 0,
                .target = {0},
                .ptr = NULL,
                .size = ret_val
            };
            if (ret_val <= 8) {
                void *buf = g2h(syscall_arg1);
                memcpy(mem_access.target, buf, ret_val);
                mem_access.observed_valid = true;
            }
            (void)snapshot_read_access(env, &mem_access);
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

/* Stage 7.4 owns fresh-target mapping/application.  The mapping request is
 * exactly the decoded aggregate extent; only the accepted payload interval
 * receives an OSPREY overwrite event. */
static target_ulong snapshot_alloc_pointer_target(CPUArchState *env,
                                                  uint64_t extent)
    G_GNUC_UNUSED;
static target_ulong snapshot_alloc_pointer_target(CPUArchState *env,
                                                  uint64_t extent)
{
    abi_long mapped;
    target_ulong target;

    (void)env;
    if (extent == 0 || extent > SNAPSHOT_PAGE_SIZE) {
        return (target_ulong)-1;
    }
    mapped = target_mmap(0, (abi_ulong)extent,
                         PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS,
                         -1, 0);
    if (mapped == -1) {
        log_msg("[mod-pointer] [alloc-error] target_mmap failed\n");
        return (target_ulong)-1;
    }
    target = (target_ulong)(abi_ulong)mapped;
    if (target == 0 || (uint64_t)(abi_ulong)target != (uint64_t)(abi_ulong)mapped) {
        log_msg("[mod-pointer] [alloc-error] target address is not representable\n");
        return (target_ulong)-1;
    }
    log_msg("[mod-pointer] [alloc] [addr %lx] [size %llu]\n",
            target, (unsigned long long)extent);
    return target;
}

static bool snapshot_test_parse_offset(const char *text, uint64_t *out)
{
    char *end = NULL;
    uint64_t value;

    if (text == NULL || text[0] == '\0' || out == NULL) {
        return false;
    }
    errno = 0;
    value = g_ascii_strtoull(text, &end, 0);
    if (errno != 0 || end == text || *end != '\0') {
        return false;
    }
    *out = value;
    return true;
}

static bool snapshot_test_address_ref_equal(
    const OspreyRuntimeAddressRef *a, const OspreyRuntimeAddressRef *b)
{
    OspreyKey a_key;
    OspreyKey b_key;

    if (a == NULL || b == NULL) {
        return false;
    }
    a_key = osprey_addr_key(&a->address);
    b_key = osprey_addr_key(&b->address);
    return osprey_key_equal(&a_key, &b_key) && a->raw == b->raw &&
           a->instance_id == b->instance_id &&
           a->prov_object_id == b->prov_object_id &&
           a->prov_generation == b->prov_generation &&
           a->valid == b->valid;
}

static bool snapshot_test_install_applied_model(void)
{
    const char *enabled = getenv("BINRADAR_OSPREY_TEST_APPLIED_STATE");
    const char *pointer_offset_text =
        getenv("BINRADAR_OSPREY_TEST_POINTER_GLOBAL_OFFSET");
    const char *null_offset_text =
        getenv("BINRADAR_OSPREY_TEST_NULL_GLOBAL_OFFSET");
    const char *late_offset_text =
        getenv("BINRADAR_OSPREY_TEST_LATE_POINTER_GLOBAL_OFFSET");
    const char *generic_offset_text =
        getenv("BINRADAR_OSPREY_TEST_GENERIC_GLOBAL_OFFSET");
    PointerAccess *selected = NULL;
    PointerAccess *selected_late = NULL;
    PrimitiveAccess *selected_null = NULL;
    PrimitiveAccess *selected_generic = NULL;
    OspreyRuntimeAddressRef *target_ref;
    OspreyRegionInstance *target_instance = NULL;
    OspreyMutationModel *model;
    OspreyMutationEntry *entries;
    uint64_t pointer_offset = 0;
    uint64_t null_offset = 0;
    uint64_t late_offset = 0;
    uint64_t generic_offset = 0;
    uint32_t entry_count;
    uint32_t same_site_instances = 0;
    uint64_t target_extent = 13;

    if (enabled == NULL || enabled[0] == '\0' || atoi(enabled) == 0 ||
        g_osprey_ctx == NULL || shared_trace_data == NULL) {
        return false;
    }
    if (!snapshot_test_parse_offset(pointer_offset_text, &pointer_offset) ||
        !snapshot_test_parse_offset(null_offset_text, &null_offset) ||
        !snapshot_test_parse_offset(late_offset_text, &late_offset) ||
        !snapshot_test_parse_offset(generic_offset_text, &generic_offset)) {
        log_msg("[osprey] [test-model] [invalid-symbol-offsets]\n");
        return false;
    }
    for (uint32_t i = 0; i < shared_trace_data->ptr_idx &&
                           i < MAX_POINTER_ACCESS; i++) {
        PointerAccess *candidate = &shared_trace_data->pointers[i];
        uint64_t offset;

        if (candidate->cell.start.valid != 1 ||
            candidate->target_ref.valid != 1 ||
            candidate->cell.start.address.region.kind !=
                OSPREY_REGION_GLOBAL) {
            continue;
        }
        offset = (uint64_t)candidate->cell.start.address.offset;
        if (offset == pointer_offset) {
            selected = candidate;
        } else if (offset == late_offset) {
            selected_late = candidate;
        }
    }
    if (selected == NULL || selected_late == NULL ||
        !snapshot_test_address_ref_equal(&selected->target_ref,
                                         &selected_late->target_ref)) {
        log_msg("[osprey] [test-model] [missing-pointer-access]\n");
        return false;
    }
    for (uint32_t i = 0; i < shared_trace_data->prim_idx &&
                           i < MAX_PRIMITIVE_ACCESS; i++) {
        PrimitiveAccess *candidate = &shared_trace_data->primitives[i];
        uint64_t offset;

        if (candidate->size != sizeof(target_ulong) ||
            candidate->cell.start.valid != 1 ||
            candidate->cell.start.address.region.kind !=
                OSPREY_REGION_GLOBAL) {
            continue;
        }
        offset = (uint64_t)candidate->cell.start.address.offset;
        if (offset == null_offset) {
            selected_null = candidate;
        } else if (offset == generic_offset) {
            selected_generic = candidate;
        }
    }
    if (selected_null == NULL || selected_generic == NULL) {
        log_msg("[osprey] [test-model] [missing-primitive-access]\n");
        return false;
    }
    target_ref = &selected->target_ref;
    for (guint i = 0; i < g_osprey_ctx->region_instances->len; i++) {
        OspreyRegionInstance *candidate = &g_array_index(
            g_osprey_ctx->region_instances, OspreyRegionInstance, i);
        OspreyKey candidate_region = osprey_region_key(&candidate->region);
        OspreyKey target_region = osprey_region_key(
            &target_ref->address.region);

        if (!osprey_key_equal(&candidate_region, &target_region)) {
            continue;
        }
        same_site_instances++;
        if (candidate->instance_id == target_ref->instance_id &&
            candidate->raw_base <= target_ref->raw &&
            target_ref->raw < candidate->raw_max &&
            candidate->prov_object_id == target_ref->prov_object_id &&
            candidate->prov_generation == target_ref->prov_generation) {
            target_instance = candidate;
        }
    }
    if (target_instance == NULL || same_site_instances < 2 ||
        target_ref->address.region.kind != OSPREY_REGION_HEAP_SITE ||
        target_ref->raw != target_instance->raw_base ||
        target_ref->address.offset != 0 ||
        target_instance->raw_max - target_ref->raw < target_extent) {
        log_msg("[osprey] [test-model] [missing-target-instance]\n");
        return false;
    }

    entry_count = 3;
    model = g_new0(OspreyMutationModel, 1);
    entries = g_new0(OspreyMutationEntry, entry_count);
    if (model == NULL || entries == NULL) {
        g_free(entries);
        g_free(model);
        return false;
    }
    const OspreyRuntimeChunkRef *cells[3] = {
        &selected->cell, &selected_late->cell, &selected_null->cell,
    };
    for (uint32_t i = 0; i < entry_count; i++) {
        entries[i].cell.address = cells[i]->start.address;
        entries[i].cell.size = sizeof(target_ulong);
        entries[i].target_base = target_ref->address;
        entries[i].extent = target_extent;
        entries[i].support = 1;
        entries[i].kind = OSPREY_MUTATION_AGGREGATE_STRUCT;
    }
    for (uint32_t i = 1; i < entry_count; i++) {
        OspreyMutationEntry value = entries[i];
        uint32_t j = i;
        while (j > 0 && value.cell.address.offset <
                          entries[j - 1].cell.address.offset) {
            entries[j] = entries[j - 1];
            j--;
        }
        entries[j] = value;
    }
    for (uint32_t i = 0; i < entry_count; i++) entries[i].ordinal = i;
    model->version = OSPREY_MUTATION_MODEL_VERSION;
    model->entry_count = entry_count;
    model->publication_valid = 1;
    model->entries = entries;
    if (g_osprey_ctx->model != NULL) {
        osprey_model_free(g_osprey_ctx->model);
        g_osprey_ctx->model = NULL;
    }
    if (g_osprey_ctx->staged_model != NULL) {
        osprey_model_free(g_osprey_ctx->staged_model);
        g_osprey_ctx->staged_model = NULL;
    }
    osprey_mutation_model_clear(g_osprey_ctx);
    g_osprey_ctx->mutation_model = model;
    g_osprey_ctx->mutation_model_ready = true;
    g_osprey_ctx->mutation_runtime_ready = false;
    g_osprey_ctx->tx_status = OSPREY_OK;
    g_osprey_ctx->tx_stage = NULL;
    g_osprey_ctx->tx_reason = NULL;
    g_osprey_ctx->tx_model_ready = true;
    log_msg("[osprey] [test-model] [cell %lx] [late-cell %lx] "
            "[null-cell %lx] [generic-cell %lx] [target %lx] "
            "[extent %llu] [same-site %u]\n",
            (unsigned long)selected->cell.start.raw,
            (unsigned long)selected_late->cell.start.raw,
            (unsigned long)selected_null->cell.start.raw,
            (unsigned long)selected_generic->cell.start.raw,
            (unsigned long)target_ref->raw,
            (unsigned long long)target_extent, same_site_instances);
    return true;
}

static bool snapshot_apply_fresh_target(CPUArchState *env,
                                        target_ulong target,
                                        const uint8_t *bytes,
                                        uint64_t extent) G_GNUC_UNUSED;
static bool snapshot_apply_fresh_target(CPUArchState *env,
                                        target_ulong target,
                                        const uint8_t *bytes,
                                        uint64_t extent)
{
    if (env == NULL || target == 0 || bytes == NULL || extent == 0 ||
        extent > SNAPSHOT_PAGE_SIZE) {
        return false;
    }
    memcpy(g2h(target), bytes, (size_t)extent);
    sem_mem_overwrite(env, target, (target_ulong)extent,
                      SEM_OP_SNAPSHOT);
    return true;
}

/* Stage 7.5 test-only observation.  The file is opt-in, append-only, and
 * outside the forkserver protocol; production runs never open it.  Keep the
 * record fixed-width and address-bearing only for the concrete child state,
 * never host pointers or model identities. */
static uint64_t snapshot_test_observation_digest(const uint8_t *bytes,
                                                 uint64_t size)
{
    uint64_t digest = 1469598103934665603ULL;
    for (uint64_t i = 0; i < size; i++) {
        digest ^= bytes[i];
        digest *= 1099511628211ULL;
    }
    return digest;
}

static void snapshot_test_observe_write(const SnapshotMutationWrite *write,
                                        target_ulong fresh_target,
                                        target_ulong before_value,
                                        bool applied)
{
    const char *path = getenv("BINRADAR_OSPREY_TEST_OBSERVATION_FILE");
    const uint8_t *observed_target = NULL;
    uint8_t cell_bytes[sizeof(target_ulong)] = {0};
    uint64_t observed_extent = 0;
    uint64_t digest = 0;
    target_ulong cell_value = 0;
    uint8_t first = 0;
    uint8_t last = 0;
    int fd;

    if (path == NULL || path[0] == '\0' || write == NULL) return;
    if (applied && fresh_target != 0 && write->target.extent != 0) {
        observed_target = g2h(fresh_target);
        observed_extent = write->target.extent;
    } else if (applied && write->target.resolved_end >
                              write->target.resolved_raw) {
        observed_target = g2h((target_ulong)write->target.resolved_raw);
        observed_extent = write->target.resolved_end -
                          write->target.resolved_raw;
    }
    if (observed_target != NULL) {
        digest = snapshot_test_observation_digest(observed_target,
                                                   observed_extent);
        first = observed_target[0];
        last = observed_target[observed_extent - 1];
    }
    if (applied) {
        size_t cell_size = MIN((size_t)write->size, sizeof(cell_bytes));
        if (write->addr < SNAPSHOT_PAGE_SIZE) {
            memcpy(cell_bytes, write->value, cell_size);
        } else {
            memcpy(cell_bytes, g2h(write->addr), cell_size);
        }
        memcpy(&cell_value, cell_bytes, sizeof(cell_value));
    }
    fd = open(path, O_WRONLY | O_CREAT | O_APPEND, 0600);
    if (fd < 0) return;
    dprintf(fd,
            "[stage7-observation] [status %s] [kind %u] [cell %lx] "
            "[before %lx] [value %lx] [target %lx] [extent %llu] "
            "[digest %016llx] [first %02x] [last %02x] "
            "[resolved_raw %lx] [resolved_end %lx]\n",
            applied ? "ok" : "apply-failure", (unsigned)write->kind,
            (unsigned long)write->addr, (unsigned long)before_value,
            (unsigned long)cell_value, (unsigned long)fresh_target,
            (unsigned long long)observed_extent,
            (unsigned long long)digest, first, last,
            (unsigned long)write->target.resolved_raw,
            (unsigned long)write->target.resolved_end);
    close(fd);
}

static int64_t snapshot_expr_index_from_ptr(const Expr *expr)
{
    uintptr_t base;
    uintptr_t end;
    uintptr_t value;

    if (expr == NULL || pool == NULL || next_free_expr == NULL) {
        return -1;
    }
    base = (uintptr_t)pool;
    end = (uintptr_t)next_free_expr;
    value = (uintptr_t)expr;
    if (value < base || value >= end ||
        ((value - base) % sizeof(Expr)) != 0) {
        return -1;
    }
    return (int64_t)((value - base) / sizeof(Expr));
}

static SnapshotMutationPlan *snapshot_mutation_new(
    const MutationCandidate *candidate, SnapshotMutationKind kind,
    const uint8_t *value, uint32_t size, uint64_t target_extent,
    const uint8_t *target_bytes)
{
    if (candidate == NULL) {
        return NULL;
    }
    const uint8_t *source_value = value != NULL ? value : candidate->value;
    return snapshot_mutation_new_descriptor(
        (target_ulong)candidate->addr, size,
        snapshot_expr_index_from_ptr(candidate->expr), -1, kind,
        source_value, target_extent, target_bytes);
}

/* Modify guest program's state based on mod_manager. */
static void mod_manager_init(SnapshotExitInfo *exit_info)
{
    if (mod_manager == NULL && !mutation_analysis_started) {
        mod_manager = g_new0(ModificationManager, 1);
        mod_manager->modifications = g_queue_new();
        mod_manager->current = NULL;
        mutation_analysis_started = true;
        /* Directed-mode query-window preservation is the only consumer that
         * needs pool pointers.  Reconstruct them from the child's scalar
         * cursors after validating both indexes; an unusable cursor drops the
         * window request instead of publishing a partially valid range. */
        int64_t query_cursor = snapshot_query_cursor_index(exit_info);
        int64_t expr_cursor = snapshot_expr_cursor_index(exit_info);
        if (query_queue != NULL && pool != NULL &&
            snapshot_query_cursor_valid(query_cursor) &&
            snapshot_expr_cursor_valid(expr_cursor)) {
            snapshot_dump_query_window(query_queue + query_cursor,
                                       pool + expr_cursor);
        } else if (binradar_query_window_file != NULL) {
            log_msg("[snapshot] [query-window] [skip] [query-cursor %lld] "
                    "[expr-cursor %lld]\n", (long long)query_cursor,
                    (long long)expr_cursor);
        }
    }
}

static void snapshot_modification_manager_free(ModificationManager *manager)
{
    if (manager == NULL) {
        return;
    }
    if (manager->modifications != NULL) {
        g_queue_free_full(manager->modifications,
                          (GDestroyNotify)snapshot_mutation_free);
    }
    snapshot_mutation_free(manager->current);
    g_free(manager);
}

static void snapshot_mutation_history_free(void)
{
    GHashTable *value_tables[] = {
        g_read_access_tainted_primitives_all,
        g_read_access_pointers_all,
    };
    GHashTable *alias_tables[] = {
        g_read_access_tainted_primitives_original,
        g_read_access_pointers_original,
    };
    for (size_t ti = 0; ti < G_N_ELEMENTS(value_tables); ti++) {
        GHashTable *table = value_tables[ti];
        if (table != NULL) {
            GHashTableIter iter;
            gpointer key, value;
            g_hash_table_iter_init(&iter, table);
            while (g_hash_table_iter_next(&iter, &key, &value)) {
                g_free(value);
            }
            g_hash_table_destroy(table);
        }
        if (ti == 0) g_read_access_tainted_primitives_all = NULL;
        if (ti == 1) g_read_access_pointers_all = NULL;
    }
    if (alias_tables[0] != NULL) {
        g_hash_table_destroy(alias_tables[0]);
        g_read_access_tainted_primitives_original = NULL;
    }
    if (alias_tables[1] != NULL) {
        g_hash_table_destroy(alias_tables[1]);
        g_read_access_pointers_original = NULL;
    }
}

static void snapshot_modification_manager_reset(bool analysis_started)
{
    snapshot_modification_manager_free(mod_manager);
    mod_manager = NULL;
    snapshot_mutation_baseline_free(snapshot_mutation_baseline);
    snapshot_mutation_baseline = NULL;
    snapshot_mutation_history_free();
    mutation_analysis_started = analysis_started;
}


bool snapshot_mutation_writable_span(target_ulong addr,
                                     uint32_t size)
{
    uint64_t end;
    target_ulong page;

    if (addr < SNAPSHOT_PAGE_SIZE || size == 0 ||
        (uint64_t)addr > UINT64_MAX - size) return false;
    end = (uint64_t)addr + size;
    if (end <= (uint64_t)addr) return false;
    page = addr & SNAPSHOT_PAGE_MASK;
    for (;;) {
        if (!is_valid_address(page, true)) return false;
        if ((uint64_t)page + SNAPSHOT_PAGE_SIZE >= end) break;
        if (page > UINT64_MAX - SNAPSHOT_PAGE_SIZE) return false;
        page += SNAPSHOT_PAGE_SIZE;
    }
    return true;
}

typedef struct SnapshotMutationApplyContext {
    CPUArchState *cpu_env;
    int remaining;
} SnapshotMutationApplyContext;

static bool snapshot_mutation_child_read_cell(void *opaque,
                                              target_ulong addr,
                                              uint32_t size,
                                              target_ulong *value_out)
{
    SnapshotMutationApplyContext *context = opaque;
    if (context == NULL || context->cpu_env == NULL || value_out == NULL) {
        return false;
    }
    *value_out = 0;
    if (addr < SNAPSHOT_PAGE_SIZE) {
        if (addr >= CPU_NB_REGS) return false;
        *value_out = context->cpu_env->regs[(size_t)addr];
        return true;
    }
    if (!snapshot_mutation_writable_span(addr, size)) return false;
    memcpy(value_out, g2h(addr), size);
    return true;
}

static target_ulong snapshot_mutation_child_allocate_target(
    void *opaque, uint64_t extent)
{
    SnapshotMutationApplyContext *context = opaque;
    return snapshot_alloc_pointer_target(context->cpu_env, extent);
}

static bool snapshot_mutation_child_initialize_target(
    void *opaque, target_ulong target, const uint8_t *bytes, uint64_t extent)
{
    SnapshotMutationApplyContext *context = opaque;
    return snapshot_apply_fresh_target(context->cpu_env, target, bytes, extent);
}

static bool snapshot_mutation_child_publish_cell(
    void *opaque, const SnapshotMutationWrite *write, const uint8_t *value)
{
    SnapshotMutationApplyContext *context = opaque;
    CPUArchState *cpu_env = context->cpu_env;
    if (write->addr < SNAPSHOT_PAGE_SIZE) {
        target_ulong reg_value = 0;
        memcpy(&reg_value, value, sizeof(reg_value));
        cpu_env->regs[(size_t)write->addr] = reg_value;
        sem_reg_overwrite(cpu_env, (int)write->addr, SEM_OP_SNAPSHOT);
        log_msg("[mod-reg] [register %ld] [size %ld] [total %d]\n",
                write->addr, write->size, context->remaining);
    } else {
        memcpy(g2h(write->addr), value, write->size);
        sem_mem_overwrite(cpu_env, write->addr, write->size,
                          SEM_OP_SNAPSHOT);
        log_msg("[mod] [addr %lx] [size %ld] [total %d]\n",
                write->addr, write->size, context->remaining);
    }
    return true;
}

static void snapshot_mutation_child_observe(
    void *opaque, const SnapshotMutationWrite *write,
    target_ulong fresh_target, target_ulong before_value, bool applied)
{
    (void)opaque;
    snapshot_test_observe_write(write, fresh_target, before_value, applied);
}

static const SnapshotMutationApplyHost snapshot_mutation_child_host = {
    .read_cell = snapshot_mutation_child_read_cell,
    .allocate_target = snapshot_mutation_child_allocate_target,
    .initialize_target = snapshot_mutation_child_initialize_target,
    .publish_cell = snapshot_mutation_child_publish_cell,
    .observe_write = snapshot_mutation_child_observe,
};

/* Called after fork to apply the immutable current plan to the child's view. */
static void snapshot_modify_memory(CPUArchState *cpu_env)
{
    SnapshotMutationApplyContext context;
    SnapshotMutationApplyResult result;

    if (mod_manager == NULL) return;
    context.cpu_env = cpu_env;
    context.remaining = g_queue_get_length(mod_manager->modifications);
    result = snapshot_mutation_apply(mod_manager->current,
                                     &snapshot_mutation_child_host,
                                     &context);
    if (result == SNAPSHOT_MUTATION_APPLY_OK) return;

    static const char *const errors[] = {
        [SNAPSHOT_MUTATION_APPLY_EMPTY] = "empty mutation plan",
        [SNAPSHOT_MUTATION_APPLY_ALLOCATION] =
            "child write staging allocation failed",
        [SNAPSHOT_MUTATION_APPLY_KIND] = "invalid mutation kind",
        [SNAPSHOT_MUTATION_APPLY_WIDTH] = "invalid mutation width",
        [SNAPSHOT_MUTATION_APPLY_TARGET] = "invalid fresh target",
        [SNAPSHOT_MUTATION_APPLY_REGISTER] = "invalid mutation register",
        [SNAPSHOT_MUTATION_APPLY_DUPLICATE_REGISTER] = "duplicate register",
        [SNAPSHOT_MUTATION_APPLY_DESTINATION] = "unwritable destination",
        [SNAPSHOT_MUTATION_APPLY_OVERLAP] = "overlapping destinations",
        [SNAPSHOT_MUTATION_APPLY_FRESH_TARGET] = "fresh target failed",
        [SNAPSHOT_MUTATION_APPLY_PUBLISH] = "mutation publication failed",
    };
    const char *message = result < G_N_ELEMENTS(errors) ? errors[result] : NULL;
    log_msg("[mod] [apply-error] %s\n", message != NULL ? message : "unknown");
    exit_with_status(1);
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

static void flip_bits(uint8_t *target, int size) {
    for (int i = 0; i < size; i++) {
        target[i] = ~target[i];
    }
}

static void snapshot_mutation_copy_value(uint8_t *dst,
                                          const MutationCandidate *source)
{
    memcpy(dst, source->value,
           sizeof(((SnapshotMutationWrite *)0)->value));
}

/* Generic primitive generation is built completely off-queue.  The source
 * candidate is never modified, and the whole batch becomes visible at once. */
static bool add_modification_primitive(GQueue *modifications,
                                       const MutationCandidate *source)
{
    if (modifications == NULL || source == NULL || source->size == 0 ||
        source->size > sizeof(((SnapshotMutationWrite *)0)->value)) {
        return false;
    }

    uint8_t values[3][sizeof(target_ulong)];
    uint8_t legacy_work[sizeof(target_ulong)];
    memset(values, 0, sizeof(values));
    snapshot_mutation_copy_value(legacy_work, source);
    uint32_t count = 0;
    uint64_t original = 0;
    memcpy(&original, source->value, source->size);

    if (source->size == 1) {
        if (original != 0) {
            legacy_work[0] = 0;
            memcpy(values[count++], legacy_work, sizeof(legacy_work));
        }
        if (original != 1) {
            memcpy(values[count], legacy_work, sizeof(legacy_work));
            values[count++][0] = 1;
        }
        flip_bits(legacy_work, source->size);
        memcpy(values[count++], legacy_work, sizeof(legacy_work));
    } else if (source->size == 2) {
        if (original != 0) {
            snapshot_mutation_copy_value(values[count], source);
            memset(values[count++], 0, source->size);
        }
        if (original != 1) {
            snapshot_mutation_copy_value(values[count], source);
            memset(values[count], 0, source->size);
            values[count++][0] = 1;
            memset(legacy_work, 0, source->size);
            legacy_work[0] = 1;
        }
        flip_bits(legacy_work, source->size);
        memcpy(values[count++], legacy_work, sizeof(legacy_work));
    } else if (source->size == 4 || source->size == 8) {
        if (original != 0) {
            snapshot_mutation_copy_value(values[count], source);
            memset(values[count], 0, source->size);
            count++;
        }
        if (original != 1) {
            snapshot_mutation_copy_value(values[count], source);
            memset(values[count], 0, source->size);
            values[count][0] = 1;
            count++;
        }
        snapshot_mutation_copy_value(values[count], source);
        flip_bits(values[count], source->size);
        count++;
    } else if (source->size < 8) {
        snapshot_mutation_copy_value(values[0], source);
        flip_bits(values[0], source->size);
        count = 1;
    } else {
        /* Preserve the existing no-op policy for unsupported widths. */
        return false;
    }

    SnapshotMutationPlan *batch[3] = {NULL, NULL, NULL};
    for (uint32_t i = 0; i < count; i++) {
        batch[i] = snapshot_mutation_new(source, SNAPSHOT_MUTATION_BYTES,
                                          values[i], source->size, 0, NULL);
        if (batch[i] == NULL) {
            snapshot_mutation_free_batch(batch, count);
            return false;
        }
    }
    return snapshot_mutation_enqueue_batch(modifications, batch, count);
}

static bool add_untyped_pointer_candidate(GQueue *modifications,
                                          const MutationCandidate *source)
{
    uint8_t null_value[sizeof(target_ulong)] = {0};
    SnapshotMutationPlan *mod = snapshot_mutation_new(
        source, SNAPSHOT_MUTATION_POINTER_NULL, null_value, source->size,
        0, NULL);
    if (mod == NULL) {
        return false;
    }
    return snapshot_mutation_enqueue_one(modifications, mod);
}

typedef enum SnapshotPointerSource {
    SNAPSHOT_POINTER_FROM_PRIMITIVE = 0,
    SNAPSHOT_POINTER_FROM_ACCESS = 1,
} SnapshotPointerSource;
/* Resolve one baseline pointer access and enqueue its complete typed batch.
 * This focused Stage 7 source lane uses the same compact resolver as the
 * production coordinator sink below; it does not adapt a decoded full model. */
static bool add_pointer_typed_candidate(
    GQueue *modifications, const MutationCandidate *source,
    const OspreyRuntimeChunkRef *cell,
    const OspreyRuntimeAddressRef *target_ref, bool typed_allowed,
    SnapshotPointerSource source_kind) G_GNUC_UNUSED;

static bool add_pointer_typed_candidate(
    GQueue *modifications, const MutationCandidate *source,
    const OspreyRuntimeChunkRef *cell,
    const OspreyRuntimeAddressRef *target_ref, bool typed_allowed,
    SnapshotPointerSource source_kind)
{
    const OspreyMutationModel *model = NULL;
    OspreyRuntimePointerResolution resolution;
    OspreyRuntimeResolveStatus status;
    uint8_t zero_value[sizeof(target_ulong)] = {0};
    target_ulong concrete_value;
    uint32_t count = 0;
    SnapshotMutationPlan *batch[3] = {NULL, NULL, NULL};

    if (!typed_allowed || source == NULL ||
        source->size != sizeof(target_ulong) || cell == NULL ||
        cell->start.valid != 1 || cell->size != source->size ||
        cell->start.raw != (uint64_t)source->addr || g_osprey_ctx == NULL ||
        !g_osprey_ctx->config.enabled || !osprey_collect_enabled ||
        !osprey_runtime_mutation_prepare(g_osprey_ctx)) {
        goto generic;
    }
    model = osprey_runtime_mutation_model(g_osprey_ctx);
    if (model == NULL) goto generic;
    memcpy(&concrete_value, source->value, sizeof(concrete_value));
    status = osprey_runtime_resolve_pointer(
        g_osprey_ctx, model, cell, concrete_value, target_ref,
        &resolution);
    if (getenv("BINRADAR_OSPREY_TEST_APPLIED_STATE") != NULL) {
        log_msg("[osprey] [test-plan] [addr %lx] [value %lx] [status %d] "
                "[extent %llu] [target-valid %u] [runtime-target %u]\n",
                (unsigned long)source->addr,
                (unsigned long)concrete_value, (int)status,
                (unsigned long long)resolution.target_extent,
                resolution.target_valid, resolution.has_runtime_target);
    }
    if (status != OSPREY_RUNTIME_RESOLVED || resolution.target_extent == 0 ||
        resolution.target_extent > SNAPSHOT_PAGE_SIZE) {
        goto generic;
    }

    if (concrete_value == 0) {
        uint8_t fills[3][SNAPSHOT_PAGE_SIZE];
        memset(fills[0], 0, sizeof(fills[0]));
        memset(fills[1], 1, sizeof(fills[1]));
        memset(fills[2], 0xff, sizeof(fills[2]));
        for (uint32_t i = 0; i < G_N_ELEMENTS(fills); i++) {
            batch[count++] = snapshot_mutation_new(
                source, SNAPSHOT_MUTATION_POINTER_FRESH, zero_value,
                sizeof(target_ulong), resolution.target_extent,
                fills[i]);
            if (batch[count - 1] == NULL) {
                snapshot_mutation_free_batch(batch, count);
                goto generic;
            }
        }
    } else {
        uint64_t target_raw;
        uint64_t target_end;
        uint64_t oob;
        target_ulong oob_value;
        uint8_t oob_bytes[sizeof(target_ulong)];

        if (!resolution.has_runtime_target || !resolution.target_valid ||
            target_ref == NULL) {
            goto generic;
        }
        target_raw = resolution.target.raw;
        if (target_raw > UINT64_MAX - resolution.target_extent) {
            goto generic;
        }
        target_end = target_raw + resolution.target_extent;
        if (target_end <= target_raw || target_end > UINT64_MAX - 0x10u) {
            goto generic;
        }
        oob = target_end + 0x10u;
        if (oob < target_end ||
            (oob >= target_raw && oob < target_end)) {
            goto generic;
        }
        oob_value = (target_ulong)oob;
        if ((uint64_t)oob_value != oob) goto generic;
        memcpy(oob_bytes, &oob_value, sizeof(oob_value));

        batch[count++] = snapshot_mutation_new(
            source, SNAPSHOT_MUTATION_POINTER_NULL, zero_value,
            sizeof(target_ulong), 0, NULL);
        batch[count++] = snapshot_mutation_new(
            source, SNAPSHOT_MUTATION_POINTER_OOB, oob_bytes,
            sizeof(target_ulong), 0, NULL);
        if (batch[0] == NULL || batch[1] == NULL) {
            snapshot_mutation_free_batch(batch, count);
            goto generic;
        }
        batch[0]->mods[0].target.resolved_raw = target_raw;
        batch[0]->mods[0].target.resolved_end = target_end;
        batch[1]->mods[0].target.resolved_raw = target_raw;
        batch[1]->mods[0].target.resolved_end = target_end;
    }
    if (snapshot_mutation_enqueue_batch(modifications, batch, count)) {
        return true;
    }

generic:
    if (source_kind == SNAPSHOT_POINTER_FROM_ACCESS) {
        return add_untyped_pointer_candidate(modifications, source);
    }
    return add_modification_primitive(modifications, source);
}

static bool snapshot_mutation_legacy_emit_family(
    SnapshotOspreyAdapter *adapter,
    const SnapshotMutationBaselineEntry *entry,
    SnapshotMutationProposalSink *sink)
{
    OspreyRuntimePointerResolution resolution;
    OspreyRuntimeResolveStatus status;
    SnapshotMutationProposalFamily family;
    SnapshotMutationProposalVariant variants[3];
    SnapshotMutationProposalWrite writes[3];
    uint8_t fills[3][SNAPSHOT_PAGE_SIZE];
    target_ulong concrete_value;
    uint32_t count;

    if (entry == NULL || sink == NULL ||
        (entry->source_kind != SNAPSHOT_MUTATION_SOURCE_PRIMITIVE &&
         entry->source_kind != SNAPSHOT_MUTATION_SOURCE_POINTER)) {
        return false;
    }
    memcpy(&concrete_value, entry->planner_bytes, sizeof(concrete_value));
    status = snapshot_osprey_adapter_resolve_pointer(
        adapter, entry, concrete_value, &resolution);
    if (getenv("BINRADAR_OSPREY_TEST_APPLIED_STATE") != NULL) {
        log_msg("[osprey] [test-plan] [addr %lx] [value %lx] [status %d] "
                "[extent %llu] [target-valid %u] [runtime-target %u]\n",
                (unsigned long)entry->addr, (unsigned long)concrete_value,
                (int)status, (unsigned long long)resolution.target_extent,
                resolution.target_valid, resolution.has_runtime_target);
    }
    if (status != OSPREY_RUNTIME_RESOLVED || resolution.target_extent == 0 ||
        resolution.target_extent > SNAPSHOT_PAGE_SIZE) {
        return false;
    }

    memset(&family, 0, sizeof(family));
    memset(variants, 0, sizeof(variants));
    memset(writes, 0, sizeof(writes));
    family.advisor_id = 1; /* first in-process advisor: OSPREY type */
    family.advisor_priority = 0;
    family.family_id = entry->token.source_ordinal;
    family.primary_seed = entry->token;
    family.seed_semantics = SNAPSHOT_MUTATION_SEED_SNAPSHOT_STATE;
    family.variants = variants;
    memset(fills, 0, sizeof(fills));

    if (concrete_value == 0) {
        memset(fills[1], 1, sizeof(fills[1]));
        memset(fills[2], 0xff, sizeof(fills[2]));
        count = 3;
        for (uint32_t i = 0; i < count; i++) {
            variants[i].variant_id = i;
            variants[i].write_count = 1;
            variants[i].writes = &writes[i];
            writes[i].destination = entry->token;
            writes[i].kind = SNAPSHOT_MUTATION_POINTER_FRESH;
            writes[i].size = sizeof(target_ulong);
            writes[i].target_extent = resolution.target_extent;
            writes[i].target_bytes = fills[i];
            memcpy(writes[i].value, entry->planner_bytes,
                   sizeof(writes[i].value));
        }
    } else {
        uint64_t target_raw;
        uint64_t target_end;
        uint64_t oob;
        target_ulong oob_value;

        if (!resolution.has_runtime_target || !resolution.target_valid ||
            !entry->target_ref_valid) {
            return false;
        }
        target_raw = resolution.target.raw;
        if (target_raw > UINT64_MAX - resolution.target_extent) return false;
        target_end = target_raw + resolution.target_extent;
        if (target_end <= target_raw || target_end > UINT64_MAX - 0x10u) {
            return false;
        }
        oob = target_end + 0x10u;
        if (oob < target_end ||
            (oob >= target_raw && oob < target_end)) return false;
        oob_value = (target_ulong)oob;
        if ((uint64_t)oob_value != oob) return false;
        count = 2;
        for (uint32_t i = 0; i < count; i++) {
            variants[i].variant_id = i;
            variants[i].write_count = 1;
            variants[i].writes = &writes[i];
            writes[i].destination = entry->token;
            writes[i].size = sizeof(target_ulong);
            writes[i].target_extent = 0;
            writes[i].target_bytes = NULL;
            writes[i].resolved_raw = target_raw;
            writes[i].resolved_end = target_end;
        }
        writes[0].kind = SNAPSHOT_MUTATION_POINTER_NULL;
        writes[1].kind = SNAPSHOT_MUTATION_POINTER_OOB;
        memcpy(writes[1].value, &oob_value, sizeof(oob_value));
    }
    family.variant_count = count;
    return snapshot_mutation_sink_submit(sink, &family);
}

static void snapshot_mutation_legacy_advisor(
    SnapshotOspreyAdapter *adapter,
    const SnapshotMutationBaseline *baseline,
    SnapshotMutationProposalSink *sink)
{
    if (adapter == NULL || baseline == NULL || sink == NULL) return;
    for (uint32_t i = 0; i < baseline->entry_count; i++) {
        (void)snapshot_mutation_legacy_emit_family(
            adapter, &baseline->entries[i], sink);
    }
}

// In parent process, called after child execution
// Return: remaining modifications
static int select_next_modification(SnapshotExitInfo *exit_info) {
    (void)exit_info;

    if (mod_manager == NULL) {
        return 0;
    }

    if (mod_manager->current != NULL) {
        snapshot_mutation_free(mod_manager->current);
        mod_manager->current = NULL;
    }
    mod_manager->current = g_queue_pop_head(mod_manager->modifications);
    if (mod_manager->current == NULL) {
        log_msg("[analyze] [done] consumed all modifications\n");
        if (shared_trace_data != NULL) {
            memset(shared_trace_data, 0, sizeof(SharedTraceData));
        }
        snapshot_modification_manager_reset(true);
        return 0;
    }

    // Finished: reset shared_trace_data
    memset(shared_trace_data, 0, sizeof(SharedTraceData));
    return g_queue_get_length(mod_manager->modifications) + 1;
}

static bool snapshot_mutation_baseline_add_history(
    const SnapshotObservationView *observations)
{
    const uint32_t prim_count = observations->primitive_count;
    const uint32_t ptr_count = observations->pointer_count;
    if (g_read_access_tainted_primitives_original == NULL) {
        g_read_access_tainted_primitives_original =
            g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        g_read_access_pointers_original =
            g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        g_read_access_tainted_primitives_all =
            g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        g_read_access_pointers_all =
            g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
    }
    for (uint32_t i = 0; i < prim_count; i++) {
        PrimitiveAccess *copy = g_try_malloc(sizeof(*copy));
        if (copy == NULL) return false;
        *copy = observations->primitives[i];
        g_hash_table_insert(g_read_access_tainted_primitives_original,
                            GSIZE_TO_POINTER(copy->addr), copy);
        g_hash_table_insert(g_read_access_tainted_primitives_all,
                            GSIZE_TO_POINTER(copy->addr), copy);
    }
    for (uint32_t i = 0; i < ptr_count; i++) {
        PointerAccess *copy = g_try_malloc(sizeof(*copy));
        if (copy == NULL) return false;
        *copy = observations->pointers[i];
        g_hash_table_insert(g_read_access_pointers_original,
                            GSIZE_TO_POINTER(copy->addr), copy);
        g_hash_table_insert(g_read_access_pointers_all,
                            GSIZE_TO_POINTER(copy->addr), copy);
    }
    return true;
}

static void snapshot_mutation_baseline_fill_common(
    SnapshotMutationBaselineEntry *entry, uint64_t epoch,
    uint32_t ordinal, SnapshotMutationLane lane,
    SnapshotMutationSourceKind source_kind, uintptr_t addr, uint32_t size,
    uintptr_t pc, uint64_t access_id, int64_t expr_index,
    int64_t query_index)
{
    memset(entry, 0, sizeof(*entry));
    entry->token.run_epoch = epoch;
    entry->token.source_ordinal = ordinal;
    entry->lane = lane;
    entry->source_kind = source_kind;
    entry->access_id = access_id;
    entry->pc = pc;
    entry->addr = (target_ulong)addr;
    entry->size = size;
    entry->eligible = true;
    entry->typed_eligible = true;
    entry->protected_addr = snapshot_addr_is_protected(entry->addr);
    entry->expr_index = expr_index;
    entry->query_index = query_index;
}

static SnapshotMutationBaseline *snapshot_mutation_baseline_build(
    const SnapshotObservationView *observations,
    const ArgumentInfo *arg_info, size_t num_arg_regs)
{
    if (observations == NULL) return NULL;
    const SnapshotExitInfo *exit_info = &observations->exit_info;
    const uint32_t prim_count = observations->primitive_count;
    const uint32_t ptr_count = observations->pointer_count;
    const bool counts_valid = observations->counts_valid;
    size_t argument_count = 0;
    size_t total;
    uint64_t epoch;
    SnapshotMutationBaseline *baseline;
    uint32_t ordinal = 0;

    for (size_t i = 0; i < num_arg_regs; i++) {
        if (arg_info != NULL && arg_info[i].expr != NULL) argument_count++;
    }
    total = (size_t)prim_count + (size_t)ptr_count + argument_count;
    if (total > UINT32_MAX || total > SIZE_MAX / sizeof(*baseline->entries)) {
        return NULL;
    }
    baseline = snapshot_mutation_try_malloc0(sizeof(*baseline));
    if (baseline == NULL) return NULL;
    epoch = observations->run_epoch;
    baseline->run_epoch = epoch;
    baseline->entry_count = (uint32_t)total;
    baseline->counts_valid = counts_valid;
    baseline->query_start = snapshot_mutation_query_start;
    baseline->query_end = snapshot_query_cursor_index(exit_info);
    baseline->expr_start = snapshot_mutation_expr_start;
    baseline->expr_end = snapshot_expr_cursor_index(exit_info);
    /* Half-open [start, end) windows over raw pool differences.  An entry
     * beyond the exit or an unpublished cursor makes the window unusable, so
     * the advisor sees no window rather than a reversed or unbounded one. */
    if (baseline->query_start < 0 || baseline->query_end < 0 ||
        baseline->query_start > baseline->query_end ||
        !snapshot_query_cursor_valid(baseline->query_end)) {
        baseline->query_start = -1;
        baseline->query_end = -1;
    }
    if (baseline->expr_start < 0 || baseline->expr_end < 0 ||
        baseline->expr_start > baseline->expr_end ||
        !snapshot_expr_cursor_valid(baseline->expr_end)) {
        baseline->expr_start = -1;
        baseline->expr_end = -1;
    }
    if (total != 0) {
        baseline->entries = snapshot_mutation_try_malloc0(
            total * sizeof(*baseline->entries));
        if (baseline->entries == NULL) {
            snapshot_mutation_baseline_free(baseline);
            return NULL;
        }
    }

    if (!snapshot_mutation_baseline_add_history(observations)) {
        snapshot_mutation_baseline_free(baseline);
        snapshot_mutation_history_free();
        return NULL;
    }

    for (uint32_t i = 0; i < prim_count; i++, ordinal++) {
        const PrimitiveAccess *source = &observations->primitives[i];
        SnapshotMutationBaselineEntry *entry = &baseline->entries[ordinal];
        bool epoch_valid = source->run_epoch == epoch;
        snapshot_mutation_baseline_fill_common(
            entry, epoch, ordinal, SNAPSHOT_MUTATION_LANE_PRIMITIVE,
            SNAPSHOT_MUTATION_SOURCE_PRIMITIVE, source->addr,
            source->size > 0 ? (uint32_t)source->size : 0, source->pc,
            source->access_id, source->expr_index, source->query_index);
        if (source->size <= 0 ||
            (uint32_t)source->size > sizeof(entry->planner_bytes)) {
            entry->eligible = false;
            entry->typed_eligible = false;
        } else {
            memcpy(entry->planner_bytes, g2h(source->addr),
                   (size_t)source->size);
        }
        if (epoch_valid && counts_valid) {
            entry->cell = source->cell;
            /* Symbolic metadata is trustworthy only inside the epoch that
             * produced it; the indexes were validated by the finalizer. */
            if (source->observed_read_valid &&
                source->expr_index >= 0 && source->query_index >= 0 &&
                source->expr_index < baseline->expr_end &&
                source->query_index >= baseline->query_start &&
                source->query_index < baseline->query_end &&
                snapshot_expr_cursor_valid(source->expr_index) &&
                snapshot_query_cursor_valid(source->query_index) &&
                source->root_extension <= SNAPSHOT_MUTATION_ROOT_SEXT) {
                memcpy(entry->observed_read_bytes,
                       source->observed_read_bytes,
                       sizeof(entry->observed_read_bytes));
                entry->observed_read_valid = true;
                entry->root_extension =
                    (SnapshotMutationRootExtension)source->root_extension;
            } else {
                entry->observed_read_valid = false;
                entry->expr_index = -1;
                entry->query_index = -1;
            }
        } else {
            memset(&entry->cell, 0, sizeof(entry->cell));
            entry->observed_read_valid = false;
            entry->expr_index = -1;
            entry->query_index = -1;
            entry->typed_eligible = false;
        }
        log_msg("[analyze] [primitive] [index %u] [addr %lx] [size %d] [id %llu]\n",
                i, source->addr, source->size,
                (unsigned long long)source->access_id);
    }
    for (uint32_t i = 0; i < ptr_count; i++, ordinal++) {
        const PointerAccess *source = &observations->pointers[i];
        SnapshotMutationBaselineEntry *entry = &baseline->entries[ordinal];
        bool epoch_valid = source->run_epoch == epoch;
        snapshot_mutation_baseline_fill_common(
            entry, epoch, ordinal, SNAPSHOT_MUTATION_LANE_POINTER,
            SNAPSHOT_MUTATION_SOURCE_POINTER, source->addr,
            sizeof(target_ulong), source->pc, source->access_id,
            source->expr_index, source->query_index);
        memcpy(entry->planner_bytes, &source->target,
               sizeof(target_ulong));
        if (epoch_valid && counts_valid) {
            entry->cell = source->cell;
            entry->target_ref = source->target_ref;
            entry->target_ref_valid = source->target != 0 &&
                                      source->target_ref.valid == 1;
            if (source->observed_read_valid &&
                source->expr_index >= 0 && source->query_index >= 0 &&
                source->expr_index < baseline->expr_end &&
                source->query_index >= baseline->query_start &&
                source->query_index < baseline->query_end &&
                snapshot_expr_cursor_valid(source->expr_index) &&
                snapshot_query_cursor_valid(source->query_index) &&
                source->root_extension <= SNAPSHOT_MUTATION_ROOT_SEXT) {
                memcpy(entry->observed_read_bytes,
                       source->observed_read_bytes,
                       sizeof(entry->observed_read_bytes));
                entry->observed_read_valid = true;
                entry->root_extension =
                    (SnapshotMutationRootExtension)source->root_extension;
            } else {
                entry->observed_read_valid = false;
                entry->expr_index = -1;
                entry->query_index = -1;
            }
        } else {
            memset(&entry->cell, 0, sizeof(entry->cell));
            memset(&entry->target_ref, 0, sizeof(entry->target_ref));
            entry->target_ref_valid = false;
            entry->observed_read_valid = false;
            entry->expr_index = -1;
            entry->query_index = -1;
            entry->typed_eligible = false;
        }
        log_msg("[analyze] [pointer] [index %u] [addr %lx] [target %lx] [id %llu]\n",
                i, source->addr, source->target,
                (unsigned long long)source->access_id);
    }
    for (size_t i = 0; i < num_arg_regs; i++) {
        const ArgumentInfo *source = &arg_info[i];
        SnapshotMutationBaselineEntry *entry;
        if (source->expr == NULL) continue;
        entry = &baseline->entries[ordinal];
        bool pointer = is_valid_address(source->value, false);
        snapshot_mutation_baseline_fill_common(
            entry, epoch, ordinal, SNAPSHOT_MUTATION_LANE_ARGUMENT,
            pointer ? SNAPSHOT_MUTATION_SOURCE_ARGUMENT_POINTER
                    : SNAPSHOT_MUTATION_SOURCE_ARGUMENT_PRIMITIVE,
            source->reg, sizeof(target_ulong), 0, i,
            snapshot_expr_index_from_ptr(source->expr), -1);
        memcpy(entry->planner_bytes, &source->value,
               sizeof(target_ulong));
        entry->eligible = !pointer;
        entry->typed_eligible = false;
        entry->protected_addr = snapshot_addr_is_protected(entry->addr);
        log_msg("[analyze] [sym-arg] [%s] [reg %zu] [expr %p]\n",
                pointer ? "ptr" : "prim", i, (void *)source->expr);
        ordinal++;
    }
    return baseline;
}

static void snapshot_mutation_candidate_from_entry(
    const SnapshotMutationBaselineEntry *entry, MutationCandidate *candidate)
{
    memset(candidate, 0, sizeof(*candidate));
    candidate->addr = entry->addr;
    candidate->size = entry->size;
    candidate->kind = entry->source_kind == SNAPSHOT_MUTATION_SOURCE_POINTER
        ? 1 : 0;
    if (entry->expr_index >= 0 && pool != NULL && next_free_expr != NULL) {
        uintptr_t index = (uintptr_t)entry->expr_index;
        uintptr_t count = ((uintptr_t)next_free_expr - (uintptr_t)pool) /
                          sizeof(Expr);
        if (index < count) candidate->expr = pool + index;
    }
    memcpy(candidate->value, entry->planner_bytes,
           sizeof(candidate->value));
}

static bool snapshot_mutation_stage_generic(
    SnapshotMutationCoordinator *coordinator,
    const SnapshotMutationBaselineEntry *entry)
{
    MutationCandidate candidate;
    GQueue *temporary;
    bool ok;

    if (entry == NULL || !entry->eligible || entry->protected_addr ||
        entry->source_kind == SNAPSHOT_MUTATION_SOURCE_ARGUMENT_POINTER) {
        return true;
    }
    snapshot_mutation_candidate_from_entry(entry, &candidate);
    temporary = g_queue_new();
    if (temporary == NULL) return false;
    if (entry->source_kind == SNAPSHOT_MUTATION_SOURCE_POINTER) {
        ok = add_untyped_pointer_candidate(temporary, &candidate);
    } else {
        ok = add_modification_primitive(temporary, &candidate);
    }
    if (!ok) {
        g_queue_free_full(temporary,
                          (GDestroyNotify)snapshot_mutation_free);
        return false;
    }
    while (!g_queue_is_empty(temporary)) {
        SnapshotMutationPlan *plan = g_queue_pop_head(temporary);
        g_ptr_array_add(coordinator->staged, plan);
    }
    g_queue_free(temporary);
    return true;
}

static bool snapshot_mutation_coordinator_build(
    SnapshotMutationBaseline *baseline, GQueue *queue)
{
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    SnapshotOspreyAdapter osprey_adapter;
    bool *specialized;

    if (baseline == NULL || queue == NULL) return false;
    if (!snapshot_mutation_coordinator_init(&coordinator, baseline)) {
        return false;
    }
    sink.coordinator = &coordinator;
    sink.advisor_id = 1;
    sink.advisor_priority = 0;
    snapshot_osprey_adapter_init(
        &osprey_adapter, g_osprey_ctx,
        g_osprey_ctx != NULL && g_osprey_ctx->config.enabled &&
            osprey_collect_enabled,
        g_osprey_ctx != NULL && g_osprey_ctx->config.analysis_mode ==
            OSPREY_ANALYSIS_MODE_MUTATION);
    if (snapshot_osprey_adapter_is_mutation_mode(&osprey_adapter)) {
        (void)snapshot_osprey_adapter_prepare(&osprey_adapter);
    }
    snapshot_mutation_legacy_advisor(&osprey_adapter, baseline, &sink);

    /* Symbolic boundary advice runs after compact OSPREY preparation and
     * before family sorting.  Capacity is decided by the per-advisor quotas,
     * not by invocation order, so a disabled advisor cannot change OSPREY's
     * accepted set. */
    if (snapshot_symbolic_mode() != SNAPSHOT_SYMBOLIC_OFF) {
        SnapshotSymbolicView view;
        SnapshotMutationProposalSink symbolic_sink;

        memset(&view, 0, sizeof(view));
        view.expr_base = pool;
        view.query_base = query_queue;
        view.expr_entry = baseline->expr_start;
        view.expr_exit = baseline->expr_end;
        view.query_entry = baseline->query_start;
        view.query_exit = baseline->query_end;
        view.baseline = baseline;
        view.run_epoch = baseline->run_epoch;
        symbolic_sink.coordinator = &coordinator;
        symbolic_sink.advisor_id = SNAPSHOT_SYMBOLIC_ADVISOR_ID;
        symbolic_sink.advisor_priority = SNAPSHOT_SYMBOLIC_ADVISOR_PRIORITY;
        if (view.expr_entry < 0 || view.expr_exit < 0 ||
            view.query_entry < 0 || view.query_exit < 0) {
            log_msg("[symbolic-advisor] [summary] [mode skip] "
                    "[reason invalid-window]\n");
        } else {
            (void)snapshot_symbolic_run(
                &view,
                snapshot_symbolic_mode() == SNAPSHOT_SYMBOLIC_BOUNDARY
                    ? &symbolic_sink : NULL);
        }
    }

    snapshot_mutation_coordinator_sort(&coordinator);
    specialized = g_try_malloc0((size_t)baseline->entry_count *
                                sizeof(*specialized));
    if (specialized == NULL && baseline->entry_count != 0) {
        snapshot_mutation_coordinator_clear(&coordinator);
        return false;
    }
    for (guint fi = 0; fi < coordinator.families->len; fi++) {
        SnapshotMutationProposalFamily *family =
            g_ptr_array_index(coordinator.families, fi);
        const SnapshotMutationBaselineEntry *primary =
            snapshot_mutation_lookup_entry(baseline, family->primary_seed);
        bool staged = snapshot_mutation_stage_family(&coordinator, family);
        if (staged && primary != NULL) {
            specialized[primary->token.source_ordinal] = true;
        }
    }
    for (uint32_t i = 0; i < baseline->entry_count; i++) {
        if (!specialized[i] &&
            !snapshot_mutation_stage_generic(&coordinator,
                                             &baseline->entries[i])) {
            g_free(specialized);
            snapshot_mutation_coordinator_clear(&coordinator);
            return false;
        }
    }
    g_free(specialized);
    bool published = snapshot_mutation_coordinator_publish(&coordinator,
                                                            queue);
    snapshot_mutation_coordinator_clear(&coordinator);
    return published;
}

static int analyze_collected_data(const ArgumentInfo *arg_info,
                                  size_t num_arg_regs)
{
    SnapshotObservationView observations;
    SnapshotExitInfo *exit_info;
    int remaining;

    if (!snapshot_observation_capture(shared_trace_data, &observations)) {
        log_msg("[analyze] [observation-error] capture failed\n");
        exit_with_status(1);
    }
    exit_info = &observations.exit_info;
    if (!exit_info->valid) {
        log_msg("[analyze] [exit-error] no exit info!!!\n");
        snapshot_observation_view_clear(&observations);
        return 0;
    }
    if (exit_info->crashed) {
        const char *host_name = exit_info->host_signal > 0
            ? strsignal(exit_info->host_signal) : NULL;
        if (exit_info->target_signal == 0) {
            log_msg("[analyze] [host-crash] [exit %d] [addr %lx] "
                    "[reason %s] [name %s] [last %lx] Host crashed!!!\n",
                    exit_info->host_signal, exit_info->host_fault_addr,
                    exit_info->description,
                    host_name != NULL ? host_name : "unknown",
                    exit_info->guest_last_translation_block);
            exit_with_status(1);
        }
        log_msg("[analyze] [crash] [exit %d] [target %d] [host %d] "
                "[name %s] [fault-addr %lx] [guest-pc %lx] [guest-cs %lx] "
                "[si-code %d] [last %lx]\n",
                exit_info->exit_code, exit_info->target_signal,
                exit_info->host_signal,
                host_name != NULL ? host_name : "unknown",
                exit_info->fault_addr, exit_info->guest_pc,
                exit_info->guest_cs_base, exit_info->si_code,
                exit_info->guest_last_translation_block);
    } else {
        log_msg("[analyze] [normal] [exit %d] [guest-pc %lx] "
                "[guest-cs %lx] [reason %s] [last %lx]\n",
                exit_info->exit_code, exit_info->guest_pc,
                exit_info->guest_cs_base, exit_info->description,
                exit_info->guest_last_translation_block);
    }

    if (!observations.counts_valid) {
        log_msg("[analyze] [count-clamp] [prim %u->%u] [ptr %u->%u] "
                "[prim-ovf %u] [ptr-ovf %u] typed-unavailable\n",
                observations.raw_primitive_count,
                observations.primitive_count,
                observations.raw_pointer_count,
                observations.pointer_count,
                observations.primitive_overflow,
                observations.pointer_overflow);
    }

    /* First run freezes the copied view.  Later iterations only retire the
     * current immutable plan; they never revisit the child-writable arrays. */
    if (!mutation_analysis_started) {
        SnapshotMutationBaseline *baseline;
        mod_manager_init(exit_info);
        original_exit_info = *exit_info;
        baseline = snapshot_mutation_baseline_build(
            &observations, arg_info, num_arg_regs);
        if (baseline == NULL) {
            log_msg("[analyze] [mutation-error] baseline allocation failed\n");
            exit_with_status(1);
        }
        snapshot_mutation_baseline_free(snapshot_mutation_baseline);
        snapshot_mutation_baseline = baseline;
        if (!snapshot_mutation_coordinator_build(
                snapshot_mutation_baseline, mod_manager->modifications)) {
            log_msg("[analyze] [mutation-error] coordinator publication failed\n");
            exit_with_status(1);
        }
        log_msg("[analyze] [baseline] [epoch %llu] [entries %u] "
                "[counts-valid %s] [query-end %lld] [expr-end %lld]\n",
                (unsigned long long)baseline->run_epoch,
                baseline->entry_count,
                baseline->counts_valid ? "true" : "false",
                (long long)baseline->query_end,
                (long long)baseline->expr_end);
        log_msg("[analyze] [queue] [len %d]\n",
                g_queue_get_length(mod_manager->modifications));
    }
    remaining = select_next_modification(exit_info);
    snapshot_observation_view_clear(&observations);
    return remaining;
}

static void snapshot_prepare_mutation_epoch(void)
{
    uint64_t epoch;
    if (shared_trace_data == NULL) return;
    /* Half-open raw pool cursors: the baseline child's query suffix and
     * expression arena start here. */
    snapshot_mutation_query_start =
        (query_queue != NULL && next_query != NULL)
            ? (int64_t)(next_query - query_queue) : -1;
    snapshot_mutation_expr_start =
        (pool != NULL && next_free_expr != NULL)
            ? (int64_t)(next_free_expr - pool) : -1;
    epoch = ++next_snapshot_mutation_epoch;
    if (epoch == 0) epoch = ++next_snapshot_mutation_epoch;
    shared_trace_data->run_epoch = epoch;
}

/* Parent-side deferred-finding reporter: after the child died (or was
 * killed on timeout), surface any provenance finding the child recorded
 * in shared memory.  Returns true if a finding was reported. */
static bool report_shared_prov_finding(void *opaque, uint32_t *status_out) {
    (void)opaque;
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
        info->valid = 0;
        info->crashed = 1;
        info->target_signal = TARGET_SIGSEGV;
        info->host_signal = 0;
        info->si_code = SEGV_ACCERR;
        info->exit_code = 139;
        info->guest_pc = f->access_pc;
        info->guest_cs_base = 0;
        snapshot_exit_info_set_fault_reference(
            info, SNAPSHOT_FAULT_REFERENCE_PROVENANCE_ACCESS,
            f->access_pc);
        info->host_fault_addr = 0;
        info->guest_last_translation_block = last_translation_block;
        info->query_cursor = (fault.finding_query_idx >= 0 &&
                              snapshot_query_cursor_valid(
                                  fault.finding_query_idx))
            ? fault.finding_query_idx
            : ((next_query != NULL && query_queue != NULL)
               ? (int64_t)(next_query - query_queue) : -1);
        info->expr_cursor = (fault.finding_expr_idx >= 0 &&
                             snapshot_expr_cursor_valid(
                                 fault.finding_expr_idx))
            ? fault.finding_expr_idx
            : ((next_free_expr != NULL && pool != NULL)
               ? (int64_t)(next_free_expr - pool) : -1);
        const char *pf_reason = provenance_fault_reason();
        g_strlcpy(info->description,
                  pf_reason ? pf_reason : "memcheck: provenance finding",
                  SNAPSHOT_EXIT_DESC_LEN);
        info->valid = 1;
        snapshot_emit_crash_rows(info);
    }
    return true;
}

void snapshot_forkserver(CPUState *cpu, CPUArchState *cpu_env,
                         const ArgumentInfo *arg_info, size_t num_arg_regs) {
    log_msg("[snapshot] [forkserver] [called %d]\n", forkserver_installed);
    if (forkserver_installed) return;
    forkserver_installed = true;
    rcu_disable_atfork();
    snapshot_save();
    BinradarForkserverDriver driver;
    if (!binradar_forkserver_driver_init(
            &driver, binradar_forkserver_ctrl_r,
            binradar_forkserver_stat_w)) {
        log_msg("[snapshot] [forkserver] [error] invalid control fds\n");
        exit_with_status(1);
    }

    bool binradar_mode = binradar_manager != NULL;
    afl_forksrv_pid = getpid();
    if (!binradar_forkserver_handshake(&driver)) {
        log_msg("[snapshot] [forkserver] [error] protocol-v3 handshake\n");
        exit_with_status(1);
    }
    log_msg("[forkserver] [start] [protocol 3]\n");

    for (;;) {
        uint32_t was_killed;
        if (!binradar_forkserver_next(&driver, &was_killed)) {
            log_msg("[forkserver] [exit] parent (fuzzolic) dead or exit\n");
            exit_with_status(2);
        }
        const uint32_t iteration = driver.iteration;
        uint32_t representative_runs = 0;
        uint32_t remaining_mods = 0;
        bool iteration_aborted = false;
        bool *uncovered = NULL;
        bool *executed = NULL;
        SnapshotExitInfo baseline_exit = {0};
        bool baseline_exit_valid = false;

        if (binradar_mode && iteration > 1) {
            uncovered = g_new0(bool, binradar_manager->patch_max_id + 1u);
            executed = g_new0(bool, binradar_manager->patch_max_id + 1u);
            for (uint32_t i = 0; i < binradar_manager->patch_cnt; i++) {
                uint32_t patch = (uint32_t)binradar_cache_patch_id_at(
                    binradar_manager, i + 1u);
                uncovered[patch] = true;
            }
        }

        uint32_t selected_patch = 0;
        for (;;) {
            uint32_t child_status = 0;
            if (binradar_mode) {
                binradar_cache_reset_child(binradar_manager);
                if (!binradar_cache_publish_selector(binradar_manager,
                                                selected_patch, iteration)) {
                    log_msg("[binradar] [cache-fatal] "
                            "[reason selector-publication]\n");
                    exit_with_status(5);
                }
                if (shared_trace_data != NULL) {
                    memset(&shared_trace_data->exit_info, 0,
                           sizeof(shared_trace_data->exit_info));
                }
                log_msg("[binradar] [shm] [patch-id %u] [iter %u]\n",
                        selected_patch, iteration);
            }

            fflush(NULL);
            trace_mem_flush();
            log_msg_flush();
            if (g_osprey_ctx != NULL && g_osprey_shared_run != NULL) {
                osprey_shared_run_prepare(g_osprey_ctx, g_osprey_shared_run,
                                          iteration);
            }
            snapshot_prepare_mutation_epoch();
            pid_t child_pid = fork();
            if (child_pid < 0) exit_with_status(4);
            if (child_pid == 0) {
#ifdef SNAPSHOT_DEBUG
                snapshot_install_crash_handler();
#endif
                snapshot_modify_memory(cpu_env);
                provenance_clear_pending_fault();
                if (g_osprey_ctx != NULL && g_osprey_shared_run != NULL) {
                    osprey_child_use_shared_run(g_osprey_ctx,
                                                g_osprey_shared_run);
                }
                afl_fork_child = 1;
                binradar_forkserver_child_close(&driver);
                return;
            }

            representative_runs++;
            int wait_rc = binradar_forkserver_wait_child(
                &driver, child_pid, binradar_manager, &child_status,
                report_shared_prov_finding, NULL);
            if (wait_rc < 0) exit_with_status(6);
            if (binradar_forkserver_record_wait(
                    &driver, wait_rc, representative_runs)) {
                iteration_aborted = true;
                break;
            }
            trace_mem_flush();

            SnapshotExitInfo *exit_info = snapshot_exit_info_ptr();
            if (binradar_mode &&
                (exit_info == NULL || !exit_info->valid ||
                 (exit_info->crashed && !exit_info->fault_reference_valid))) {
                log_msg("[binradar] [iteration-discarded] [iter %u] "
                        "[reason unusable-exit] [patch %u]\n",
                        iteration, selected_patch);
                iteration_aborted = true;
                break;
            }
            if (binradar_mode) {
                binradar_cache_record_outcome(
                    binradar_manager, selected_patch,
                    snapshot_exit_info_ptr());
                if (executed != NULL && selected_patch != 0) {
                    executed[selected_patch] = true;
                }
            }
            if (binradar_mode && selected_patch == 0) {
                baseline_exit = *exit_info;
                baseline_exit_valid = true;
            }

            if (wait_rc == 0 && g_osprey_ctx != NULL &&
                g_osprey_shared_run != NULL && g_osprey_ctx->config.enabled &&
                binradar_mode && iteration == 1 && selected_patch == 0) {
                OspreyStatus merged = osprey_parent_merge_sample(
                    g_osprey_ctx, g_osprey_shared_run);
                if (merged != OSPREY_OK && merged != OSPREY_DISABLED) {
                    log_msg("[forkserver] [osprey] [merge-failed] "
                            "[status %d]\n", (int)merged);
                }
            }

            if (binradar_mode && binradar_manager->cache_enabled) {
                PatchedResult *observed = binradar_cache_result(
                    binradar_manager, selected_patch);
                GArray *selected_vector = NULL;
                bool selected_valid =
                    !binradar_manager->cache_capture_overflow &&
                    binradar_cache_vector(binradar_manager, selected_patch,
                                          selected_patch,
                                          &selected_vector) &&
                    binradar_cache_observed_matches(observed->br_taken,
                                                     selected_vector);
                if (!selected_valid) {
                    if (selected_vector != NULL) {
                        g_array_free(selected_vector, TRUE);
                    }
                    if (binradar_manager->feedback_dir != NULL) {
                        log_msg("[binradar] [feedback] [error snapshot] "
                                "[iter %u] [patch %u]\n",
                                iteration, selected_patch);
                        exit_with_status(1);
                    }
                    if (binradar_manager->cache_inference_enabled) {
                        binradar_cache_disable(binradar_manager,
                                               "representative-mismatch");
                        binradar_cache_restore_uncovered(
                            binradar_manager, uncovered, executed);
                    }
                } else {
                    const SnapshotMutationPlan *feedback_plan =
                        mod_manager != NULL ? mod_manager->current : NULL;
                    const BinradarMutationFeedbackView mutation_view = {
                        .writes = feedback_plan != NULL
                            ? feedback_plan->mods : NULL,
                        .write_count = feedback_plan != NULL
                            ? feedback_plan->num_mods : 0,
                    };
                    if (!binradar_cache_feedback_write(
                            binradar_manager, iteration, selected_patch,
                            selected_vector, &mutation_view)) {
                        g_array_free(selected_vector, TRUE);
                        exit_with_status(1);
                    }
                    if (binradar_manager->cache_inference_enabled &&
                        iteration > 1) {
                        for (uint32_t i = 0;
                             i < binradar_manager->patch_cnt; i++) {
                            uint32_t candidate =
                                (uint32_t)binradar_cache_patch_id_at(
                                    binradar_manager, i + 1u);
                            if (!uncovered[candidate] ||
                                candidate == selected_patch) continue;
                            GArray *candidate_vector = NULL;
                            if (!binradar_cache_vector(
                                    binradar_manager, selected_patch,
                                    candidate, &candidate_vector)) {
                                binradar_cache_disable(
                                    binradar_manager,
                                    "candidate-evaluation");
                                binradar_cache_restore_uncovered(
                                    binradar_manager, uncovered, executed);
                                break;
                            }
                            if (binradar_cache_observed_matches(
                                    observed->br_taken, candidate_vector)) {
                                binradar_cache_materialize(
                                    binradar_manager, candidate,
                                    selected_patch, candidate_vector,
                                    snapshot_exit_info_ptr());
                                uncovered[candidate] = false;
                            }
                            g_array_free(candidate_vector, TRUE);
                        }
                    }
                    g_array_free(selected_vector, TRUE);
                }
            }

            if (!binradar_mode || iteration == 1) break;
            if (selected_patch != 0) uncovered[selected_patch] = false;
            selected_patch = 0;
            for (uint32_t i = 0; i < binradar_manager->patch_cnt; i++) {
                uint32_t candidate =
                    (uint32_t)binradar_cache_patch_id_at(
                        binradar_manager, i + 1u);
                if (uncovered[candidate]) {
                    selected_patch = candidate;
                    break;
                }
            }
            if (selected_patch == 0) break;
        }

        if (binradar_mode) {
            if (iteration_aborted || !baseline_exit_valid) {
                binradar_cache_clear_iteration(binradar_manager);
                remaining_mods = 0;
            } else {
                *snapshot_exit_info_ptr() = baseline_exit;
                if (iteration == 1) {
                    if (g_osprey_ctx != NULL && g_osprey_ctx->config.enabled &&
                        osprey_tx_ok(g_osprey_ctx)) {
                        if (!snapshot_test_install_applied_model()) {
                            osprey_analyze(g_osprey_ctx);
                        }
                    }
                    remaining_mods = analyze_collected_data(
                        arg_info, num_arg_regs);
                } else {
                    if (!binradar_cache_commit(binradar_manager)) {
                        exit_with_status(1);
                    }
                    remaining_mods = analyze_collected_data(
                        arg_info, num_arg_regs);
                }
                if (iteration == 1 &&
                    !binradar_cache_commit(binradar_manager)) {
                    exit_with_status(1);
                }
            }
        }
        g_free(executed);
        g_free(uncovered);

        if (!binradar_forkserver_send_summary(
                &driver, representative_runs, remaining_mods)) {
            exit_with_status(7);
        }
    }
}

SnapshotMemRegion *mr_manager_heap_search_pub(target_ulong addr) { return mr_manager_heap_search(addr); }
