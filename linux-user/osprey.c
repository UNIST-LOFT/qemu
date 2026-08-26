/*
 * OSPREY lifecycle, configuration, shared-run transport, and region
 * resolution.  See osprey.h for the public API and the ownership model.
 *
 * The child side writes fixed-layout fact records into a MAP_SHARED
 * OspreySharedRun; the parent merges them into committed in-memory
 * tables after the child exits (osprey_parent_merge_sample in
 * osprey-facts.c).  The shared run is reset by the forkserver parent
 * before every fork.
 */

#include "osprey.h"
#include "osprey-internal.h"

#include "qemu/thread.h"

#include <stdlib.h>
#include <string.h>

/* Key allocation helpers (osprey-internal.h declares the struct). */
OspreyKey *osprey_key_new(const OspreyKey *k) {
    OspreyKey *copy = g_new(OspreyKey, 1);
    *copy = *k;
    return copy;
}

void osprey_key_free(gpointer p) {
    g_free(p);
}

/* Collection enable flag read by the translator wrappers
 * (osprey_active() in translate.c).  Set from BINRADAR_OSPREY_ENABLE at
 * snapshot init; stays 0 in all other modes so translated code pays no
 * branch cost. */
int osprey_collect_enabled = 0;

/* osprey_free_cpu_origins is defined below; osprey_run_table and
 * osprey_get_image_base are declared in osprey-internal.h. */
void osprey_free_cpu_origins(void);

/* Module-global pre-sample fatal state (defined below with the image
 * helpers; used by osprey_shared_run_reset and osprey_new above it). */
static bool g_pre_sample_fatal;
static const char *g_pre_sample_reason;

/* ------------------------------------------------------------------ */
/* Configuration                                                       */
/* ------------------------------------------------------------------ */

#define OSPREY_DEFAULT_SHARED_MB 64u
#define OSPREY_DEFAULT_MAX_FACTS 262144u
#define OSPREY_DEFAULT_MAX_CHUNKS_PER_REGION 8192u
#define OSPREY_DEFAULT_MAX_CANDIDATES_PER_KIND_REGION 4096u
#define OSPREY_DEFAULT_MAX_VARIABLES 100000u
#define OSPREY_DEFAULT_MAX_FACTORS 500000u
#define OSPREY_DEFAULT_MAX_EXACT_CLIQUE_VARS 20u
#define OSPREY_DEFAULT_REPORT_THRESHOLD 0.6

static bool osprey_parse_u64(const char *name, uint64_t *out) {
    const char *v = getenv(name);
    if (v == NULL || v[0] == '\0') {
        return true;
    }
    char *end = NULL;
    errno = 0;
    unsigned long long val = strtoull(v, &end, 10);
    if (errno == ERANGE || end == v || *end != '\0' || val > INT64_MAX) {
        fprintf(stderr, "[osprey] [config] [invalid] [var %s] [value %s]\n",
                name, v);
        return false;
    }
    *out = (uint64_t)val;
    return true;
}

bool osprey_config_from_env(OspreyConfig *config) {
    memset(config, 0, sizeof(*config));
    config->enabled = false;
    config->shared_bytes = OSPREY_DEFAULT_SHARED_MB * 1024u * 1024u;
    config->max_facts = OSPREY_DEFAULT_MAX_FACTS;
    config->max_chunks_per_region = OSPREY_DEFAULT_MAX_CHUNKS_PER_REGION;
    config->max_candidates_per_kind_region =
        OSPREY_DEFAULT_MAX_CANDIDATES_PER_KIND_REGION;
    config->max_variables = OSPREY_DEFAULT_MAX_VARIABLES;
    config->max_factors = OSPREY_DEFAULT_MAX_FACTORS;
    config->max_exact_clique_vars = OSPREY_DEFAULT_MAX_EXACT_CLIQUE_VARS;
    config->report_threshold = OSPREY_DEFAULT_REPORT_THRESHOLD;

    const char *v = getenv("BINRADAR_OSPREY_ENABLE");
    config->enabled = (v != NULL && v[0] != '\0' && atoi(v) != 0);

    uint64_t tmp = 0;
    if (!osprey_parse_u64("BINRADAR_OSPREY_SHARED_MB", &tmp)) return false;
    if (tmp != 0) {
        if (tmp > 4096) {
            fprintf(stderr,
                    "[osprey] [config] [too-large] [var BINRADAR_OSPREY_SHARED_MB] [value %llu]\n",
                    (unsigned long long)tmp);
            return false;
        }
        config->shared_bytes = tmp * 1024u * 1024u;
    }
    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_FACTS", &tmp)) return false;
    if (tmp != 0) config->max_facts = tmp;
    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_CHUNKS_PER_REGION", &tmp)) return false;
    if (tmp != 0) config->max_chunks_per_region = tmp;
    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_CANDIDATES_PER_KIND_REGION", &tmp)) return false;
    if (tmp != 0) config->max_candidates_per_kind_region = tmp;
    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_VARIABLES", &tmp)) return false;
    if (tmp != 0) config->max_variables = tmp;
    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_FACTORS", &tmp)) return false;
    if (tmp != 0) config->max_factors = tmp;
    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_EXACT_CLIQUE_VARS", &tmp)) return false;
    if (tmp != 0) config->max_exact_clique_vars = tmp;

    v = getenv("BINRADAR_OSPREY_REPORT_THRESHOLD");
    if (v != NULL && v[0] != '\0') {
        char *end = NULL;
        double d = strtod(v, &end);
        if (end == v || *end != '\0' || d < 0.0 || d > 1.0) {
            fprintf(stderr,
                    "[osprey] [config] [invalid] [var BINRADAR_OSPREY_REPORT_THRESHOLD] [value %s]\n",
                    v);
            return false;
        }
        config->report_threshold = d;
    }

    v = getenv("BINRADAR_OSPREY_DUMP_FILE");
    if (v != NULL && v[0] != '\0') {
        snprintf(config->dump_file, sizeof(config->dump_file), "%s", v);
    }
    return true;
}

/* ------------------------------------------------------------------ */
/* Shared-run layout                                                   */
/* ------------------------------------------------------------------ */

/* Record size/alignment per table. */
static size_t table_record_size(int table) {
    switch (table) {
    case OSPREY_TABLE_ACCESS: return sizeof(OspreyAccessFact);
    case OSPREY_TABLE_BASE: return sizeof(OspreyBaseFact);
    case OSPREY_TABLE_COPY: return sizeof(OspreyCopyFact);
    case OSPREY_TABLE_POINTS: return sizeof(OspreyPointsToFact);
    case OSPREY_TABLE_ALLOC: return sizeof(OspreyMallocFact);
    case OSPREY_TABLE_MAYARR: return sizeof(OspreyMayArrayFact);
    default: return sizeof(OspreyRegionInstance);
    }
}

static size_t table_record_align(int table) {
    switch (table) {
    case OSPREY_TABLE_ACCESS: return _Alignof(OspreyAccessFact);
    case OSPREY_TABLE_BASE: return _Alignof(OspreyBaseFact);
    case OSPREY_TABLE_COPY: return _Alignof(OspreyCopyFact);
    case OSPREY_TABLE_POINTS: return _Alignof(OspreyPointsToFact);
    case OSPREY_TABLE_ALLOC: return _Alignof(OspreyMallocFact);
    case OSPREY_TABLE_MAYARR: return _Alignof(OspreyMayArrayFact);
    default: return _Alignof(OspreyRegionInstance);
    }
}

static uint32_t cap_for_table(const OspreyConfig *config, int table,
                              uint64_t *bytes) {
    size_t record = table_record_size(table);
    uint64_t per_table = config->shared_bytes / OSPREY_TABLE_COUNT;
    uint64_t by_records = per_table / record;
    uint64_t by_facts = config->max_facts / OSPREY_TABLE_COUNT;
    uint64_t cap = by_records < by_facts ? by_records : by_facts;
    if (cap < 64) cap = 64;
    if (cap > UINT32_MAX - 1) cap = UINT32_MAX - 1;
    if (bytes != NULL) {
        *bytes = cap * record;
    }
    return (uint32_t)cap;
}

/* One computation of the full layout: returns total byte size and fills
 * the per-table capacities and storage offsets. */
static size_t osprey_run_layout(const OspreyConfig *config,
                                uint32_t caps[OSPREY_TABLE_COUNT],
                                size_t offs[OSPREY_TABLE_COUNT]) {
    size_t base = sizeof(OspreySharedRun);
    size_t align = _Alignof(OspreySharedRun);
    base = (base + align - 1) & ~(align - 1);

    size_t off = base;
    for (int i = 0; i < OSPREY_TABLE_COUNT; i++) {
        caps[i] = cap_for_table(config, i, NULL);
        size_t a = table_record_align(i);
        off = (off + a - 1) & ~(a - 1);
        offs[i] = off;
        off += (size_t)caps[i] * table_record_size(i);
    }
    return off;
}

size_t osprey_shared_run_size(const OspreyConfig *config) {
    uint32_t caps[OSPREY_TABLE_COUNT];
    size_t offs[OSPREY_TABLE_COUNT];
    return osprey_run_layout(config, caps, offs);
}

bool osprey_shared_run_layout_valid(const OspreyConfig *config,
                                    const OspreySharedRun *run) {
    if (config == NULL || run == NULL) return false;
    uint32_t caps[OSPREY_TABLE_COUNT];
    size_t offs[OSPREY_TABLE_COUNT];
    osprey_run_layout(config, caps, offs);
    return run->access_cap == caps[OSPREY_TABLE_ACCESS] &&
           run->base_cap == caps[OSPREY_TABLE_BASE] &&
           run->copy_cap == caps[OSPREY_TABLE_COPY] &&
           run->points_cap == caps[OSPREY_TABLE_POINTS] &&
           run->alloc_cap == caps[OSPREY_TABLE_ALLOC] &&
           run->mayarray_cap == caps[OSPREY_TABLE_MAYARR] &&
           run->region_cap == caps[OSPREY_TABLE_REGION];
}

/* Storage offset of a table, computed from the capacities stored in the
 * run (set by osprey_shared_run_reset). */
static size_t run_table_offset(const OspreySharedRun *run, int table) {
    size_t base = sizeof(OspreySharedRun);
    size_t align = _Alignof(OspreySharedRun);
    base = (base + align - 1) & ~(align - 1);
    uint32_t caps[OSPREY_TABLE_COUNT] = {
        run->access_cap, run->base_cap, run->copy_cap,
        run->points_cap, run->alloc_cap, run->mayarray_cap,
        run->region_cap,
    };
    size_t off = base;
    for (int i = 0; i < table; i++) {
        size_t a = table_record_align(i);
        off = (off + a - 1) & ~(a - 1);
        off += (size_t)caps[i] * table_record_size(i);
    }
    size_t a = table_record_align(table);
    off = (off + a - 1) & ~(a - 1);
    return off;
}

uint8_t *osprey_run_table(OspreySharedRun *run, int table) {
    return (uint8_t *)run + run_table_offset(run, table);
}

void osprey_shared_run_reset(OspreySharedRun *run, uint64_t sample_id,
                             const OspreyConfig *config) {
    memset(run, 0, sizeof(*run));
    run->version = OSPREY_SHARED_VERSION;
    run->sample_id = (uint32_t)sample_id;
    run->first_dropped_hash = 0;

    /* Pre-sample fatal state (e.g. ELF/global registration overflow)
     * is copied into every reset shared run so the baseline merge
     * rejects fail-closed; silent range omission is never acceptance. */
    if (g_pre_sample_fatal) {
        run->bad_arithmetic = 1;
    }

    uint32_t caps[OSPREY_TABLE_COUNT];
    size_t offs[OSPREY_TABLE_COUNT];
    size_t total = osprey_run_layout(config, caps, offs);
    run->region_cap = caps[OSPREY_TABLE_REGION];
    run->region_used = 0;

    run->access_cap = caps[OSPREY_TABLE_ACCESS];
    run->base_cap = caps[OSPREY_TABLE_BASE];
    run->copy_cap = caps[OSPREY_TABLE_COPY];
    run->points_cap = caps[OSPREY_TABLE_POINTS];
    run->alloc_cap = caps[OSPREY_TABLE_ALLOC];
    run->mayarray_cap = caps[OSPREY_TABLE_MAYARR];

    /* Zero the table storage (open addressing needs zeroed keys). */
    size_t off = offs[OSPREY_TABLE_ACCESS];
    memset((uint8_t *)run + off, 0, total - off);
}

/* ------------------------------------------------------------------ */
/* Context lifecycle                                                   */
/* ------------------------------------------------------------------ */

OspreyContext *osprey_new(const OspreyConfig *config) {
    OspreyContext *ctx = g_new0(OspreyContext, 1);
    ctx->config = *config;
    /* Copy the module-global pre-sample fatal state (set by
     * registration-time failures that precede context creation) into
     * the context. */
    ctx->pre_sample_fatal = g_pre_sample_fatal;
    ctx->pre_sample_reason = g_pre_sample_reason;
    qemu_mutex_init(&ctx->shared_lock);
    ctx->global_ranges = g_array_new(FALSE, FALSE, sizeof(OspreyGlobalRange));
    ctx->access_facts = g_array_new(FALSE, FALSE, sizeof(OspreyAccessFact));
    ctx->base_facts = g_array_new(FALSE, FALSE, sizeof(OspreyBaseFact));
    ctx->copy_facts = g_array_new(FALSE, FALSE, sizeof(OspreyCopyFact));
    ctx->points_facts = g_array_new(FALSE, FALSE, sizeof(OspreyPointsToFact));
    ctx->alloc_facts = g_array_new(FALSE, FALSE, sizeof(OspreyMallocFact));
    ctx->mayarray_facts = g_array_new(FALSE, FALSE, sizeof(OspreyMayArrayFact));
    ctx->region_instances = g_array_new(FALSE, FALSE,
                                        sizeof(OspreyRegionInstance));
    ctx->runtime_regions = g_array_new(FALSE, FALSE, sizeof(OspreyRuntimeRegion));
    ctx->last_status = OSPREY_DISABLED;
    ctx->tx_status = OSPREY_DISABLED;
    ctx->tx_stage = NULL;
    ctx->tx_reason = NULL;
    ctx->tx_model_ready = false;
    ctx->staged_graph = NULL;
    ctx->staged_model = NULL;
    osprey_ctx_ref_set(ctx);
    return ctx;
}

void osprey_free(OspreyContext *ctx) {
    if (ctx == NULL) return;
    osprey_tx_abort(ctx);
    if (ctx->global_ranges != NULL) {
        g_array_free(ctx->global_ranges, TRUE);
    }
    g_array_free(ctx->access_facts, TRUE);
    g_array_free(ctx->base_facts, TRUE);
    g_array_free(ctx->copy_facts, TRUE);
    g_array_free(ctx->points_facts, TRUE);
    g_array_free(ctx->alloc_facts, TRUE);
    g_array_free(ctx->mayarray_facts, TRUE);
    g_array_free(ctx->runtime_regions, TRUE);
    g_array_free(ctx->region_instances, TRUE);
    osprey_free_cpu_origins();
    osprey_free_runtime_regions();
    if (ctx->graph) {
        osprey_graph_free(ctx->graph);
    }
    if (ctx->model) {
        osprey_model_free(ctx->model);
    }
    qemu_mutex_destroy(&ctx->shared_lock);
    osprey_ctx_ref_set(NULL);
    g_free(ctx);
}

/* ------------------------------------------------------------------ */
/* Main-image writable global ranges (merged interval set)             */
/* ------------------------------------------------------------------ */

/* Sorted by base; adjacent/overlapping ranges are merged.  Offsets are
 * image-relative (base - image_base). */
void global_ranges_add(OspreyContext *ctx, target_ulong base,
                       uint64_t size) {
    if (ctx == NULL || size == 0) return;
    target_ulong image_base = osprey_get_image_base();
    if (image_base == 0 || base < image_base ||
        (uint64_t)(base - image_base) > INT64_MAX || size > INT64_MAX) {
        osprey_mark_pre_sample_fatal(ctx,
            "global range outside image or exceeds INT64_MAX");
        return;
    }
    int64_t off = (int64_t)(base - image_base);
    if (off > INT64_MAX - (int64_t)size) {
        osprey_mark_pre_sample_fatal(ctx,
            "global range offset+size overflow");
        return;
    }
    OspreyGlobalRange r;
    r.offset = off;
    r.extent = size;
    GArray *a = ctx->global_ranges;
    /* Merge with every overlapping/adjacent range (a new range can
     * bridge several existing ones), then insert at the sorted
     * position. */
    int64_t lo = r.offset;
    int64_t hi = r.offset + (int64_t)r.extent;
    guint i = 0;
    while (i < a->len) {
        OspreyGlobalRange *e = &g_array_index(a, OspreyGlobalRange, i);
        int64_t e_hi = e->offset + (int64_t)e->extent;
        if (hi < e->offset) break;          /* r entirely before e */
        if (lo > e_hi) { i++; continue; }   /* r entirely after e */
        /* overlap/adjacent: absorb e into r */
        if (e->offset < lo) lo = e->offset;
        if (e_hi > hi) hi = e_hi;
        g_array_remove_index(a, i);
    }
    r.offset = lo;
    r.extent = (uint64_t)(hi - lo);
    guint j = 0;
    while (j < a->len &&
           g_array_index(a, OspreyGlobalRange, j).offset < r.offset) {
        j++;
    }
    g_array_insert_val(a, j, r);
}

/* Resolve a runtime address into the main-image global region. */
bool osprey_global_of_addr(target_ulong addr, OspreyRegionId *region,
                           int64_t *offset) {
    OspreyContext *ctx = osprey_ctx_ref();
    if (ctx == NULL || ctx->global_ranges == NULL) return false;
    target_ulong image_base = osprey_get_image_base();
    if (image_base == 0 || addr < image_base ||
        (uint64_t)(addr - image_base) > INT64_MAX) {
        return false;
    }
    int64_t off = (int64_t)(addr - image_base);
    for (guint i = 0; i < ctx->global_ranges->len; i++) {
        const OspreyGlobalRange *e = &g_array_index(
            ctx->global_ranges, OspreyGlobalRange, i);
        if (off < e->offset) return false;
        if (e->extent <= INT64_MAX &&
            e->offset <= INT64_MAX - (int64_t)e->extent &&
            off < e->offset + (int64_t)e->extent) {
            region->kind = OSPREY_REGION_GLOBAL;
            region->code_image_id = 0;
            region->site_offset = 0;
            *offset = off;
            return true;
        }
    }
    return false;
}

/* Module-level context pointer for child-side helpers (set by
 * osprey_child_use_shared_run; cleared on teardown). */
static OspreyContext *g_osprey_ctx_ref = NULL;

OspreyContext *osprey_ctx_ref(void) { return g_osprey_ctx_ref; }

void osprey_ctx_ref_set(OspreyContext *ctx) { g_osprey_ctx_ref = ctx; }

/* Module-level image base; set from elfload before the context exists. */
static target_ulong osprey_image_base;
static target_ulong osprey_image_end;

void osprey_set_image_base(target_ulong base) {
    osprey_image_base = base;
    osprey_image_end = 0;
}

target_ulong osprey_get_image_base(void) { return osprey_image_base; }

void osprey_set_image_bounds(target_ulong start, target_ulong end) {
    osprey_image_base = start;
    osprey_image_end = end > start ? end : 0;
}

target_ulong osprey_get_image_end(void) { return osprey_image_end; }

/* Module-global pre-sample fatal state: registration-time arithmetic
 * failures (global_ranges_add) can precede the OspreyContext creation
 * (elfload runs before snapshot_init), so the reason is stored here,
 * copied into the context at creation, and mirrored into every reset
 * shared run. */
static bool g_pre_sample_fatal = false;
static const char *g_pre_sample_reason = NULL;

void osprey_mark_pre_sample_fatal(OspreyContext *ctx, const char *reason) {
    g_pre_sample_fatal = true;
    g_pre_sample_reason = reason;
    if (ctx != NULL) {
        ctx->pre_sample_fatal = true;
        ctx->pre_sample_reason = reason;
    }
}

void osprey_clear_pre_sample_fatal(void) {
    g_pre_sample_fatal = false;
    g_pre_sample_reason = NULL;
}

/* ------------------------------------------------------------------ */
/* Origin shadows (per-CPU; module-level, single-threaded TCG)         */
/* ------------------------------------------------------------------ */

static GHashTable *g_cpu_origins = NULL; /* env* -> OspreyCpuOriginState* */

OspreyCpuOriginState *osprey_cpu_origin(CPUArchState *env) {
    if (g_cpu_origins == NULL) {
        g_cpu_origins = g_hash_table_new_full(g_direct_hash, g_direct_equal,
                                              NULL, NULL);
    }
    OspreyCpuOriginState *st = g_hash_table_lookup(g_cpu_origins, env);
    if (st == NULL) {
        st = g_new0(OspreyCpuOriginState, 1);
        st->mem_slots = g_hash_table_new_full(g_direct_hash, g_direct_equal,
                                              NULL, g_free);
        g_hash_table_insert(g_cpu_origins, env, st);
    }
    return st;
}

void osprey_free_cpu_origins(void) {
    if (g_cpu_origins == NULL) return;
    GHashTableIter it;
    gpointer k, v;
    g_hash_table_iter_init(&it, g_cpu_origins);
    while (g_hash_table_iter_next(&it, &k, &v)) {
        OspreyCpuOriginState *st = v;
        if (st->mem_slots != NULL) {
            g_hash_table_destroy(st->mem_slots);
        }
        g_free(st);
    }
    g_hash_table_destroy(g_cpu_origins);
    g_cpu_origins = NULL;
}

/* ------------------------------------------------------------------ */
/* Checked arithmetic                                                  */
/* ------------------------------------------------------------------ */

bool osprey_check_add(int64_t a, int64_t b, int64_t *out) {
    if ((b > 0 && a > INT64_MAX - b) || (b < 0 && a < INT64_MIN - b)) {
        return false;
    }
    *out = a + b;
    return true;
}

bool osprey_check_sub(int64_t a, int64_t b, int64_t *out) {
    if ((b < 0 && a > INT64_MAX + b) || (b > 0 && a < INT64_MIN + b)) {
        return false;
    }
    *out = a - b;
    return true;
}

bool osprey_check_mul(uint64_t a, uint64_t b, uint64_t *out) {
    if (a != 0 && b > UINT64_MAX / a) {
        return false;
    }
    *out = a * b;
    return true;
}
