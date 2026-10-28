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

#include <math.h>
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
#define OSPREY_DEFAULT_MAX_EXACT_TABLE_MB 256u
#define OSPREY_MAX_EXACT_TABLE_MB 4096u
#define OSPREY_DEFAULT_MAX_BP_TABLE_MB 256u
#define OSPREY_MAX_BP_TABLE_MB 4096u
#define OSPREY_DEFAULT_MAX_ANALYSIS_WORK 10000000ULL
#define OSPREY_DEFAULT_MAX_PARENT_FACTS 1048576ULL
#define OSPREY_DEFAULT_MAX_PARENT_CHUNKS 1048576ULL
#define OSPREY_DEFAULT_MAX_PARENT_REGIONS 65536ULL
#define OSPREY_DEFAULT_MAX_MUTATION_INPUT 1048576ULL
#define OSPREY_DEFAULT_MAX_MUTATION_WORK 10000000ULL
#define OSPREY_DEFAULT_MAX_MUTATION_BYTES (64ULL * 1024ULL * 1024ULL)
#define OSPREY_DEFAULT_REPORT_THRESHOLD 0.6

/* Diagnostic sink (snapshot.c). */
void log_msg(const char *fmt, ...);

static bool osprey_parse_u64(const char *name, uint64_t *out) {
    if (out == NULL) {
        return false;
    }
    *out = 0;
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

static bool osprey_parse_dump_path(const char *name, char *out,
                                   size_t out_size)
{
    const char *value;
    size_t length;

    if (name == NULL || out == NULL || out_size == 0) return false;
    value = getenv(name);
    if (value == NULL || value[0] == '\0') return true;
    length = strlen(value);
    if (length >= out_size) {
        fprintf(stderr,
                "[osprey] [config] [invalid] [var %s] [reason path-too-long]\n",
                name);
        return false;
    }
    memcpy(out, value, length + 1);
    return true;
}

bool osprey_config_from_env(OspreyConfig *config) {
    if (config == NULL) return false;
    memset(config, 0, sizeof(*config));
    config->enabled = false;
    /* Environment-configured tracers use the bounded facts-only path.  A
     * zeroed direct OspreyConfig remains full mode for existing research
     * unit callers; those callers must opt into mutation explicitly. */
    config->analysis_mode = OSPREY_ANALYSIS_MODE_MUTATION;
    config->shared_bytes = OSPREY_DEFAULT_SHARED_MB * 1024u * 1024u;
    config->max_facts = OSPREY_DEFAULT_MAX_FACTS;
    config->max_chunks_per_region = OSPREY_DEFAULT_MAX_CHUNKS_PER_REGION;
    config->max_candidates_per_kind_region =
        OSPREY_DEFAULT_MAX_CANDIDATES_PER_KIND_REGION;
    config->max_variables = OSPREY_DEFAULT_MAX_VARIABLES;
    config->max_factors = OSPREY_DEFAULT_MAX_FACTORS;
    config->max_exact_clique_vars = OSPREY_DEFAULT_MAX_EXACT_CLIQUE_VARS;
    config->max_exact_table_bytes =
        (uint64_t)OSPREY_DEFAULT_MAX_EXACT_TABLE_MB * 1024u * 1024u;
    config->max_bp_table_bytes =
        (uint64_t)OSPREY_DEFAULT_MAX_BP_TABLE_MB * 1024u * 1024u;
    config->max_analysis_work = OSPREY_DEFAULT_MAX_ANALYSIS_WORK;
    config->analysis_deadline_ms = 0;
    config->max_parent_facts = OSPREY_DEFAULT_MAX_PARENT_FACTS;
    config->max_parent_chunks = OSPREY_DEFAULT_MAX_PARENT_CHUNKS;
    config->max_parent_regions = OSPREY_DEFAULT_MAX_PARENT_REGIONS;
    config->max_mutation_input = OSPREY_DEFAULT_MAX_MUTATION_INPUT;
    config->max_mutation_work = OSPREY_DEFAULT_MAX_MUTATION_WORK;
    config->max_mutation_bytes = OSPREY_DEFAULT_MAX_MUTATION_BYTES;
    config->report_threshold = OSPREY_DEFAULT_REPORT_THRESHOLD;

    const char *v = getenv("BINRADAR_OSPREY_ENABLE");
    config->enabled = (v != NULL && v[0] != '\0' && atoi(v) != 0);

    v = getenv("BINRADAR_OSPREY_ANALYSIS_MODE");
    if (v != NULL && v[0] != '\0') {
        if (strcmp(v, "mutation") == 0) {
            config->analysis_mode = OSPREY_ANALYSIS_MODE_MUTATION;
        } else if (strcmp(v, "full") == 0) {
            config->analysis_mode = OSPREY_ANALYSIS_MODE_FULL;
        } else {
            fprintf(stderr,
                    "[osprey] [config] [invalid] [var BINRADAR_OSPREY_ANALYSIS_MODE] [value %s]\n",
                    v);
            return false;
        }
    }

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

    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_ANALYSIS_WORK", &tmp)) return false;
    if (tmp != 0) config->max_analysis_work = tmp;
    if (!osprey_parse_u64("BINRADAR_OSPREY_ANALYSIS_DEADLINE_MS", &tmp)) return false;
    config->analysis_deadline_ms = tmp;
    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_PARENT_FACTS", &tmp)) return false;
    if (tmp != 0) config->max_parent_facts = tmp;
    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_PARENT_CHUNKS", &tmp)) return false;
    if (tmp != 0) config->max_parent_chunks = tmp;
    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_PARENT_REGIONS", &tmp)) return false;
    if (tmp != 0) config->max_parent_regions = tmp;
    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_MUTATION_INPUT", &tmp)) return false;
    if (tmp != 0) config->max_mutation_input = tmp;
    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_MUTATION_WORK", &tmp)) return false;
    if (tmp != 0) config->max_mutation_work = tmp;
    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_MUTATION_BYTES", &tmp)) return false;
    if (tmp != 0) config->max_mutation_bytes = tmp;

    if (!osprey_parse_u64("BINRADAR_OSPREY_MAX_EXACT_CLIQUE_VARS", &tmp)) return false;
    if (tmp != 0) {
        uint64_t width_bits = (uint64_t)sizeof(size_t) * 8u;
        if (width_bits > sizeof(uint64_t) * 8u) {
            width_bits = sizeof(uint64_t) * 8u;
        }
        if (tmp >= width_bits) {
            fprintf(stderr,
                    "[osprey] [config] [too-large] [var BINRADAR_OSPREY_MAX_EXACT_CLIQUE_VARS] [value %llu]\n",
                    (unsigned long long)tmp);
            return false;
        }
        config->max_exact_clique_vars = tmp;
    }

    v = getenv("BINRADAR_OSPREY_MAX_EXACT_TABLE_MB");
    if (v != NULL && v[0] != '\0') {
        char *end = NULL;
        errno = 0;
        unsigned long long mb = strtoull(v, &end, 10);
        if (errno == ERANGE || end == v || *end != '\0' || mb == 0 ||
            mb > OSPREY_MAX_EXACT_TABLE_MB ||
            mb > SIZE_MAX / (1024u * 1024u)) {
            fprintf(stderr,
                    "[osprey] [config] [invalid] [var BINRADAR_OSPREY_MAX_EXACT_TABLE_MB] [value %s]\n",
                    v);
            return false;
        }
        config->max_exact_table_bytes =
            (uint64_t)mb * 1024u * 1024u;
    }

    v = getenv("BINRADAR_OSPREY_MAX_BP_TABLE_MB");
    if (v != NULL && v[0] != '\0') {
        char *end = NULL;
        errno = 0;
        unsigned long long mb = strtoull(v, &end, 10);
        if (v[0] < '0' || v[0] > '9' || errno == ERANGE ||
            end == v || *end != '\0' || mb == 0 ||
            mb > OSPREY_MAX_BP_TABLE_MB ||
            mb > SIZE_MAX / (1024u * 1024u)) {
            fprintf(stderr,
                    "[osprey] [config] [invalid] [var BINRADAR_OSPREY_MAX_BP_TABLE_MB] [value %s]\n",
                    v);
            return false;
        }
        config->max_bp_table_bytes = (uint64_t)mb * 1024u * 1024u;
    }

    v = getenv("BINRADAR_OSPREY_REPORT_THRESHOLD");
    if (v != NULL && v[0] != '\0') {
        char *end = NULL;
        errno = 0;
        double d = strtod(v, &end);
        if (errno == ERANGE || end == v || *end != '\0' ||
            !isfinite(d) || d < 0.0 || d > 1.0) {
            fprintf(stderr,
                    "[osprey] [config] [invalid] [var BINRADAR_OSPREY_REPORT_THRESHOLD] [value %s]\n",
                    v);
            return false;
        }
        config->report_threshold = d;
    }

    if (!osprey_parse_dump_path("BINRADAR_OSPREY_DUMP_FILE",
                                config->dump_file,
                                sizeof(config->dump_file)) ||
        !osprey_parse_dump_path("BINRADAR_OSPREY_GRAPH_DUMP_FILE",
                                config->graph_dump_file,
                                sizeof(config->graph_dump_file)) ||
        !osprey_parse_dump_path("BINRADAR_OSPREY_MODEL_DUMP_FILE",
                                config->model_dump_file,
                                sizeof(config->model_dump_file))) {
        return false;
    }
    return true;
}

static const char *osprey_budget_stage_name(OspreyAnalysisStage stage)
{
    static const char *const names[OSPREY_ANALYSIS_STAGE_COUNT] = {
        "merge", "relations", "stage3", "infer", "decode"
    };
    return stage < OSPREY_ANALYSIS_STAGE_COUNT ? names[stage] : "unknown";
}

static const char *osprey_budget_unit_name(OspreyBudgetUnit unit)
{
    static const char *const names[OSPREY_BUDGET_UNIT_COUNT] = {
        "relation-probe", "rule-probe", "candidate", "predicate",
        "factor", "edge", "graph-growth", "union-find-growth", "closure",
        "inference-update", "decode-object", "parent-preflight"
    };
    return unit < OSPREY_BUDGET_UNIT_COUNT ? names[unit] : "unknown";
}

static uint64_t osprey_elapsed_ms(int64_t start_us, int64_t end_us)
{
    if (start_us < 0 || end_us <= start_us) return 0;
    return (uint64_t)(end_us - start_us) / 1000u;
}

static void osprey_budget_reject(OspreyContext *ctx,
                                 OspreyAnalysisStage stage,
                                 const char *reason)
{
    if (ctx == NULL || ctx->analysis_budget_exhausted) return;
    ctx->analysis_budget_exhausted = true;
    ctx->analysis_budget_reason = reason;
    osprey_tx_reject(ctx, OSPREY_LIMIT_EXCEEDED,
                     osprey_budget_stage_name(stage), reason);
}

void osprey_budget_begin(OspreyContext *ctx)
{
    if (ctx == NULL) return;
    memset(ctx->analysis_stage_work, 0, sizeof(ctx->analysis_stage_work));
    memset(ctx->analysis_unit_work, 0, sizeof(ctx->analysis_unit_work));
    memset(ctx->analysis_stage_started_us, 0,
           sizeof(ctx->analysis_stage_started_us));
    memset(ctx->analysis_stage_start_work, 0,
           sizeof(ctx->analysis_stage_start_work));
    ctx->analysis_active = true;
    ctx->analysis_budget_exhausted = false;
    ctx->analysis_budget_reason = NULL;
    ctx->analysis_work_used = 0;
    ctx->analysis_started_us = g_get_monotonic_time();
    if (ctx->analysis_epoch != UINT64_MAX) ctx->analysis_epoch++;
}

bool osprey_budget_checkpoint(OspreyContext *ctx,
                              OspreyAnalysisStage stage)
{
    if (ctx == NULL || !ctx->analysis_active) return true;
    if (ctx->analysis_budget_exhausted || !osprey_tx_ok(ctx)) return false;
    if (ctx->config.analysis_deadline_ms != 0) {
        int64_t now = g_get_monotonic_time();
        int64_t elapsed = now - ctx->analysis_started_us;
        uint64_t deadline_us = ctx->config.analysis_deadline_ms >
                               INT64_MAX / 1000
            ? UINT64_MAX
            : ctx->config.analysis_deadline_ms * 1000;
        if (elapsed >= 0 && (uint64_t)elapsed >= deadline_us) {
            osprey_budget_reject(ctx, stage, "analysis-deadline");
            return false;
        }
    }
    return true;
}

bool osprey_budget_charge(OspreyContext *ctx, OspreyAnalysisStage stage,
                          OspreyBudgetUnit unit, uint64_t units)
{
    if (ctx == NULL || !ctx->analysis_active) return true;
    if (!osprey_budget_checkpoint(ctx, stage)) return false;
    if (stage >= OSPREY_ANALYSIS_STAGE_COUNT ||
        unit >= OSPREY_BUDGET_UNIT_COUNT || units == 0) {
        return units == 0;
    }
    if (units > UINT64_MAX - ctx->analysis_work_used ||
        units > UINT64_MAX - ctx->analysis_stage_work[stage] ||
        units > UINT64_MAX - ctx->analysis_unit_work[unit]) {
        osprey_budget_reject(ctx, stage, "analysis-work-budget");
        return false;
    }
    if (ctx->config.max_analysis_work != 0 &&
        units > ctx->config.max_analysis_work - ctx->analysis_work_used) {
        log_msg("[osprey] [budget] [exhausted] [stage %s] [unit %s] "
                "[used %llu] [limit %llu]\n",
                osprey_budget_stage_name(stage), osprey_budget_unit_name(unit),
                (unsigned long long)ctx->analysis_work_used,
                (unsigned long long)ctx->config.max_analysis_work);
        osprey_budget_reject(ctx, stage, "analysis-work-budget");
        return false;
    }
    ctx->analysis_work_used += units;
    ctx->analysis_stage_work[stage] += units;
    ctx->analysis_unit_work[unit] += units;
    /* Avoid a clock read on every unit while still checking cooperatively. */
    if ((ctx->analysis_work_used & 1023u) == 0 &&
        !osprey_budget_checkpoint(ctx, stage)) return false;
    return true;
}

void osprey_budget_stage_begin(OspreyContext *ctx, OspreyAnalysisStage stage)
{
    if (ctx == NULL || stage >= OSPREY_ANALYSIS_STAGE_COUNT) return;
    if (!ctx->analysis_active) osprey_budget_begin(ctx);
    ctx->analysis_stage_started_us[stage] = g_get_monotonic_time();
    ctx->analysis_stage_start_work[stage] = ctx->analysis_work_used;
}

void osprey_budget_stage_end(OspreyContext *ctx, OspreyAnalysisStage stage,
                             OspreyStatus status, uint64_t retained)
{
    if (ctx == NULL || stage >= OSPREY_ANALYSIS_STAGE_COUNT) return;
    int64_t now = g_get_monotonic_time();
    int64_t started = ctx->analysis_stage_started_us[stage];
    uint64_t start_work = ctx->analysis_stage_start_work[stage];
    uint64_t work = ctx->analysis_work_used >= start_work
        ? ctx->analysis_work_used - start_work : 0;
    log_msg("[osprey] [analysis] [stage %s] [elapsed_ms %llu] [work %llu] "
            "[retained %llu] [status %d] [reason %s]\n",
            osprey_budget_stage_name(stage),
            (unsigned long long)osprey_elapsed_ms(started, now),
            (unsigned long long)work, (unsigned long long)retained,
            (int)status,
            ctx->tx_reason != NULL ? ctx->tx_reason : "none");
}

void osprey_budget_finish(OspreyContext *ctx, OspreyStatus status)
{
    if (ctx == NULL || !ctx->analysis_active) return;
    int64_t now = g_get_monotonic_time();
    ctx->last_analyze_time_ms = osprey_elapsed_ms(ctx->analysis_started_us, now);
    log_msg("[osprey] [analysis] [total] [elapsed_ms %llu] [work %llu] "
            "[status %d] [reason %s]\n",
            (unsigned long long)ctx->last_analyze_time_ms,
            (unsigned long long)ctx->analysis_work_used, (int)status,
            ctx->tx_reason != NULL ? ctx->tx_reason : "none");
    ctx->analysis_active = false;
}

/* ------------------------------------------------------------------ */
/* Shared-run layout                                                   */
/* ------------------------------------------------------------------ */

/* Record size/alignment per table.  Prefix-family ids map to their
 * primary counterpart (same record format). */
static int primary_table_of(int table) {
    if (table >= OSPREY_TABLE_PREFIX_ACCESS &&
        table < OSPREY_TABLE_PREFIX_ACCESS + OSPREY_PREFIX_TABLE_COUNT) {
        return table - OSPREY_TABLE_PREFIX_ACCESS;
    }
    return table;
}

static size_t table_record_size(int table) {
    switch (primary_table_of(table)) {
    case OSPREY_TABLE_ACCESS: return sizeof(OspreyAccessFact);
    case OSPREY_TABLE_BASE: return sizeof(OspreyBaseFact);
    case OSPREY_TABLE_COPY: return sizeof(OspreyCopyFact);
    case OSPREY_TABLE_POINTS: return sizeof(OspreyPointsToFact);
    case OSPREY_TABLE_ALLOC: return sizeof(OspreyMallocFact);
    case OSPREY_TABLE_MAYARR: return sizeof(OspreyMayArrayFact);
    case OSPREY_TABLE_REGION: return sizeof(OspreyRegionInstance);
    case OSPREY_TABLE_CENSUS_CHUNK: return sizeof(OspreyCensusChunk);
    default: return sizeof(OspreyCensusRegion);
    }
}

static size_t table_record_align(int table) {
    switch (primary_table_of(table)) {
    case OSPREY_TABLE_ACCESS: return _Alignof(OspreyAccessFact);
    case OSPREY_TABLE_BASE: return _Alignof(OspreyBaseFact);
    case OSPREY_TABLE_COPY: return _Alignof(OspreyCopyFact);
    case OSPREY_TABLE_POINTS: return _Alignof(OspreyPointsToFact);
    case OSPREY_TABLE_ALLOC: return _Alignof(OspreyMallocFact);
    case OSPREY_TABLE_MAYARR: return _Alignof(OspreyMayArrayFact);
    case OSPREY_TABLE_REGION: return _Alignof(OspreyRegionInstance);
    case OSPREY_TABLE_CENSUS_CHUNK: return _Alignof(OspreyCensusChunk);
    default: return _Alignof(OspreyCensusRegion);
    }
}

/* Primary tables: the per-child (suffix) family.  The shared run also
 * carries a frozen prefix family (same capacities) and two census
 * tables; see osprey_run_layout. */

/* Table capacities per family are equal; one capacity value per
 * primary/census table is stored in the run header. */
static uint32_t cap_for_table(const OspreyConfig *config, int table,
                              uint64_t *bytes) {
    size_t record = table_record_size(table);
    uint64_t per_table = config->shared_bytes /
        (OSPREY_TABLE_COUNT + OSPREY_PREFIX_TABLE_COUNT);
    uint64_t by_records = per_table / record;
    uint64_t by_facts = config->max_facts;
    uint64_t cap = by_records < by_facts ? by_records : by_facts;
    if (cap < 64) cap = 64;
    if (cap > UINT32_MAX - 1) cap = UINT32_MAX - 1;
    if (bytes != NULL) {
        *bytes = cap * record;
    }
    return (uint32_t)cap;
}

/* Census capacities: bounded by the byte budget (like primary tables)
 * and by max_facts (unique chunks per sample; the region census holds
 * one record per unique region, and the per-region unique-chunk limit
 * is enforced separately by explicit count checks). */
static uint32_t census_cap_for_table(const OspreyConfig *config, int table,
                                     uint64_t *bytes) {
    size_t record = table_record_size(table);
    uint64_t per_table = config->shared_bytes /
        (OSPREY_TABLE_COUNT + OSPREY_PREFIX_TABLE_COUNT);
    uint64_t by_records = per_table / record;
    /* One fact can name two chunks (F03 copy), so either census may need
     * up to twice the fact count.  The byte budget remains authoritative. */
    uint64_t by_facts = config->max_facts > UINT64_MAX / 2
        ? UINT64_MAX : config->max_facts * 2;
    uint64_t cap = by_records < by_facts ? by_records : by_facts;
    if (cap < 64) cap = 64;
    if (cap > UINT32_MAX - 1) cap = UINT32_MAX - 1;
    if (bytes != NULL) {
        *bytes = cap * record;
    }
    return (uint32_t)cap;
}

/* One computation of the full layout: returns total byte size and fills
 * the per-table capacities and storage offsets.  The layout is:
 *   header
 *   primary tables (7)        -- per-child suffix
 *   prefix tables (7)         -- frozen pre-snapshot family
 *   census chunk / census region
 * All open-addressed with zeroed-key slots.  `offs` must have
 * OSPREY_LAYOUT_SLOTS entries (primary + prefix + census). */
#define OSPREY_LAYOUT_SLOTS (OSPREY_TABLE_COUNT + OSPREY_PREFIX_TABLE_COUNT)
static size_t osprey_run_layout(const OspreyConfig *config,
                                uint32_t caps[OSPREY_TABLE_COUNT],
                                size_t offs[OSPREY_LAYOUT_SLOTS]) {
    size_t base = sizeof(OspreySharedRun);
    size_t align = _Alignof(OspreySharedRun);
    base = (base + align - 1) & ~(align - 1);

    size_t off = base;
    for (int i = 0; i < OSPREY_TABLE_PRIMARY_COUNT; i++) {
        caps[i] = cap_for_table(config, i, NULL);
        size_t a = table_record_align(i);
        off = (off + a - 1) & ~(a - 1);
        offs[i] = off;
        off += (size_t)caps[i] * table_record_size(i);
    }
    /* Prefix family: same capacities, one table per primary kind. */
    for (int i = 0; i < OSPREY_TABLE_PRIMARY_COUNT; i++) {
        size_t a = table_record_align(i);
        off = (off + a - 1) & ~(a - 1);
        offs[OSPREY_TABLE_PREFIX_ACCESS + i] = off;
        off += (size_t)caps[i] * table_record_size(i);
    }
    /* Census tables. */
    for (int i = OSPREY_TABLE_CENSUS_CHUNK; i < OSPREY_TABLE_COUNT; i++) {
        caps[i] = census_cap_for_table(config, i, NULL);
        size_t a = table_record_align(i);
        off = (off + a - 1) & ~(a - 1);
        offs[i] = off;
        off += (size_t)caps[i] * table_record_size(i);
    }
    return off;
}

size_t osprey_shared_run_size(const OspreyConfig *config) {
    uint32_t caps[OSPREY_TABLE_COUNT];
    size_t offs[OSPREY_LAYOUT_SLOTS];
    return osprey_run_layout(config, caps, offs);
}

bool osprey_shared_run_layout_valid(const OspreyConfig *config,
                                    const OspreySharedRun *run) {
    if (config == NULL || run == NULL) return false;
    uint32_t caps[OSPREY_TABLE_COUNT];
    size_t offs[OSPREY_LAYOUT_SLOTS];
    osprey_run_layout(config, caps, offs);
    return run->access_cap == caps[OSPREY_TABLE_ACCESS] &&
           run->base_cap == caps[OSPREY_TABLE_BASE] &&
           run->copy_cap == caps[OSPREY_TABLE_COPY] &&
           run->points_cap == caps[OSPREY_TABLE_POINTS] &&
           run->alloc_cap == caps[OSPREY_TABLE_ALLOC] &&
           run->mayarray_cap == caps[OSPREY_TABLE_MAYARR] &&
           run->region_cap == caps[OSPREY_TABLE_REGION] &&
           run->census_chunk_cap == caps[OSPREY_TABLE_CENSUS_CHUNK] &&
           run->census_region_cap == caps[OSPREY_TABLE_CENSUS_REGION] &&
           run->max_facts_cfg == config->max_facts &&
           run->max_chunks_cfg == config->max_chunks_per_region &&
           run->prefix_frozen <= 1;
}

/* Capacity of any table family (primary, prefix, census) from the run
 * header caps. */
static uint32_t table_cap_of_run(const OspreySharedRun *run, int table) {
    switch (table) {
    case OSPREY_TABLE_ACCESS:
    case OSPREY_TABLE_PREFIX_ACCESS: return run->access_cap;
    case OSPREY_TABLE_BASE:
    case OSPREY_TABLE_PREFIX_BASE: return run->base_cap;
    case OSPREY_TABLE_COPY:
    case OSPREY_TABLE_PREFIX_COPY: return run->copy_cap;
    case OSPREY_TABLE_POINTS:
    case OSPREY_TABLE_PREFIX_POINTS: return run->points_cap;
    case OSPREY_TABLE_ALLOC:
    case OSPREY_TABLE_PREFIX_ALLOC: return run->alloc_cap;
    case OSPREY_TABLE_MAYARR:
    case OSPREY_TABLE_PREFIX_MAYARR: return run->mayarray_cap;
    case OSPREY_TABLE_REGION:
    case OSPREY_TABLE_PREFIX_REGION: return run->region_cap;
    case OSPREY_TABLE_CENSUS_CHUNK: return run->census_chunk_cap;
    default: return run->census_region_cap;
    }
}

/* Storage offset of a table, computed from the capacities stored in the
 * run (set by osprey_shared_run_reset).  Accepts primary tables and the
 * prefix/census families. */
static size_t run_table_offset(const OspreySharedRun *run, int table) {
    size_t base = (sizeof(OspreySharedRun) + _Alignof(OspreySharedRun) - 1) &
                  ~(_Alignof(OspreySharedRun) - 1);
    size_t off = base;
    /* Walk the layout in declaration order: primary, prefix, census. */
    int walk[OSPREY_LAYOUT_SLOTS];
    int n = 0;
    for (int i = 0; i < OSPREY_TABLE_PRIMARY_COUNT; i++) {
        walk[n++] = i;
    }
    for (int i = 0; i < OSPREY_TABLE_PRIMARY_COUNT; i++) {
        walk[n++] = OSPREY_TABLE_PREFIX_ACCESS + i;
    }
    for (int i = OSPREY_TABLE_CENSUS_CHUNK; i < OSPREY_TABLE_COUNT; i++) {
        walk[n++] = i;
    }
    for (int i = 0; i < n; i++) {
        int t = walk[i];
        size_t a = table_record_align(t);
        off = (off + a - 1) & ~(a - 1);
        if (t == table) {
            return off;
        }
        off += (size_t)table_cap_of_run(run, t) * table_record_size(t);
    }
    return off;
}

uint8_t *osprey_run_table(OspreySharedRun *run, int table) {
    return (uint8_t *)run + run_table_offset(run, table);
}

/* Occupied open slots in a prefix table. */
uint32_t osprey_run_prefix_used(const OspreySharedRun *run, int table) {
    uint32_t cap = table_cap_of_run(run, table);
    if (cap == 0) return 0;
    uint8_t *base = osprey_run_table((OspreySharedRun *)run, table);
    size_t rec_size = table_record_size(table);
    uint32_t used = 0;
    for (uint32_t slot = 0; slot < cap; slot++) {
        uint8_t *ent = base + (size_t)slot * rec_size;
        bool empty = true;
        for (size_t i = 0; i < rec_size; i++) {
            if (ent[i] != 0) {
                empty = false;
                break;
            }
        }
        if (!empty) {
            used++;
        }
    }
    return used;
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
    size_t offs[OSPREY_LAYOUT_SLOTS];
    size_t total = osprey_run_layout(config, caps, offs);
    run->access_cap = caps[OSPREY_TABLE_ACCESS];
    run->base_cap = caps[OSPREY_TABLE_BASE];
    run->copy_cap = caps[OSPREY_TABLE_COPY];
    run->points_cap = caps[OSPREY_TABLE_POINTS];
    run->alloc_cap = caps[OSPREY_TABLE_ALLOC];
    run->mayarray_cap = caps[OSPREY_TABLE_MAYARR];
    run->region_cap = caps[OSPREY_TABLE_REGION];
    run->census_chunk_cap = caps[OSPREY_TABLE_CENSUS_CHUNK];
    run->census_region_cap = caps[OSPREY_TABLE_CENSUS_REGION];
    run->max_facts_cfg = config->max_facts;
    run->max_chunks_cfg = config->max_chunks_per_region;

    /* Zero the whole table storage (open addressing needs zeroed keys):
     * primary + prefix + census families. */
    size_t off = offs[OSPREY_TABLE_ACCESS];
    memset((uint8_t *)run + off, 0, total - off);
}

/* Freeze the current primary contents as the pre-snapshot prefix.  The
 * primary tables keep their contents; the child suffix then continues
 * appending.  Facts present in both parts merge with sample_support 1.
 * Returns false when the run was already frozen or is malformed. */
bool osprey_shared_run_freeze_prefix(OspreyContext *ctx,
                                     OspreySharedRun *run) {
    if (ctx == NULL || run == NULL) return false;
    if (run->prefix_frozen) return true;
    if (run->version != OSPREY_SHARED_VERSION) {
        osprey_mark_pre_sample_fatal(ctx, "prefix freeze version mismatch");
        run->bad_arithmetic = 1;
        return false;
    }
    if (!osprey_shared_run_layout_valid(&ctx->config, run)) {
        osprey_mark_pre_sample_fatal(ctx, "prefix freeze layout mismatch");
        run->bad_arithmetic = 1;
        return false;
    }
    uint64_t prefix_count = (uint64_t)run->access_used + run->base_used +
        run->copy_used + run->points_used + run->alloc_used +
        run->mayarray_used + run->region_used;
    if (prefix_count != run->total_facts_count) {
        osprey_mark_pre_sample_fatal(ctx, "prefix fact count mismatch");
        run->bad_arithmetic = 1;
        return false;
    }
    for (int i = 0; i < OSPREY_TABLE_PRIMARY_COUNT; i++) {
        int pref = OSPREY_TABLE_PREFIX_ACCESS + i;
        uint32_t cap = table_cap_of_run(run, pref);
        uint8_t *src = osprey_run_table(run, i);
        uint8_t *dst = osprey_run_table(run, pref);
        size_t rec_size = table_record_size(i);
        memcpy(dst, src, (size_t)cap * rec_size);
        /* The primary tables now hold the frozen records; clear them so
         * the child suffix starts empty.  total_facts_count is NOT
         * reset: the prefix facts still count toward the per-sample
         * unique-fact cap (union = prefix ∪ suffix). */
        memset(src, 0, (size_t)cap * rec_size);
    }
    /* Reset the primary-table used counters (their storage was moved to
     * the prefix family) and the suffix dynamic counter; the child
     * suffix then counts only post-snapshot observations.  Capture the
     * prefix dynamic total first. */
    run->total_dynamic_prefix = run->total_dynamic_observations;
    run->total_dynamic_observations = 0;
    run->access_used = 0;
    run->base_used = 0;
    run->copy_used = 0;
    run->points_used = 0;
    run->alloc_used = 0;
    run->mayarray_used = 0;
    run->region_used = 0;
    run->prefix_frozen = 1;
    run->prefix_access_used = osprey_run_prefix_used(
        run, OSPREY_TABLE_PREFIX_ACCESS);
    run->prefix_base_used = osprey_run_prefix_used(
        run, OSPREY_TABLE_PREFIX_BASE);
    run->prefix_copy_used = osprey_run_prefix_used(
        run, OSPREY_TABLE_PREFIX_COPY);
    run->prefix_points_used = osprey_run_prefix_used(
        run, OSPREY_TABLE_PREFIX_POINTS);
    run->prefix_alloc_used = osprey_run_prefix_used(
        run, OSPREY_TABLE_PREFIX_ALLOC);
    run->prefix_mayarray_used = osprey_run_prefix_used(
        run, OSPREY_TABLE_PREFIX_MAYARR);
    run->prefix_region_used = osprey_run_prefix_used(
        run, OSPREY_TABLE_PREFIX_REGION);
    run->prefix_facts_count = prefix_count;
    run->prefix_overflow = run->overflow;
    run->prefix_bad_region = run->bad_region;
    run->prefix_bad_arithmetic = run->bad_arithmetic;
    run->prefix_bad_identity = run->bad_identity;
    run->prefix_unsupported_execution = run->unsupported_execution;
    run->prefix_first_dropped_kind = run->first_dropped_kind;
    run->prefix_first_dropped_hash = run->first_dropped_hash;
    return true;
}

/* Reset the per-child suffix only, preserving the frozen prefix.  This
 * is what the forkserver parent calls before the baseline fork: the
 * child inherits prefix + empty suffix and contributes exactly the
 * post-snapshot facts.  When no prefix is frozen (plain/unit path) the
 * whole run is reset. */
void osprey_shared_run_prepare(OspreyContext *ctx, OspreySharedRun *run,
                               uint64_t sample_id) {
    if (ctx == NULL || run == NULL) return;
    if (run->version != OSPREY_SHARED_VERSION ||
        !osprey_shared_run_layout_valid(&ctx->config, run)) {
        osprey_mark_pre_sample_fatal(ctx, "shared-run prepare mismatch");
        osprey_shared_run_reset(run, sample_id, &ctx->config);
        return;
    }
    if (!run->prefix_frozen) {
        osprey_shared_run_reset(run, sample_id, &ctx->config);
        return;
    }
    run->sample_id = (uint32_t)sample_id;
    /* The sample's unique-fact count is the union of the frozen prefix
     * (already counted before prepare) and the child suffix: keep the
     * prefix count, the child inserts continue it. */
    run->total_dynamic_observations = 0;
    run->total_facts_count = run->prefix_facts_count;
    run->overflow = run->prefix_overflow;
    run->bad_region = run->prefix_bad_region;
    run->bad_arithmetic = run->prefix_bad_arithmetic;
    run->bad_identity = run->prefix_bad_identity;
    run->unsupported_execution = run->prefix_unsupported_execution;
    run->first_dropped_kind = run->prefix_first_dropped_kind;
    run->first_dropped_hash = run->prefix_first_dropped_hash;
    if (g_pre_sample_fatal) {
        run->bad_arithmetic = 1;
    }
    run->access_used = 0;
    run->base_used = 0;
    run->copy_used = 0;
    run->points_used = 0;
    run->alloc_used = 0;
    run->mayarray_used = 0;
    run->region_used = 0;
    /* The census tables are per-sample: rebuild them from the frozen
     * prefix so this sample's census is exactly `prefix ∪ (empty
     * suffix)`; the child's suffix inserts then extend the union. */
    osprey_census_rebuild_from_prefix(run);
    /* Zero the suffix family storage only (from the end of the header
     * to the start of the prefix family). */
    uint32_t caps[OSPREY_TABLE_COUNT];
    size_t offs[OSPREY_LAYOUT_SLOTS];
    osprey_run_layout(&ctx->config, caps, offs);
    size_t primary_bytes = offs[OSPREY_TABLE_PREFIX_ACCESS] -
                           offs[OSPREY_TABLE_ACCESS];
    memset((uint8_t *)run + offs[OSPREY_TABLE_ACCESS], 0, primary_bytes);
}

/* Rebuild the per-sample census tables from the frozen prefix family.
 * Called by prepare so every forked sample starts with exactly the
 * prefix's census (unique chunks and per-region chunk counts), then the
 * child's suffix inserts extend the union. */
void osprey_census_rebuild_from_prefix(OspreySharedRun *run) {
    if (run == NULL || !run->prefix_frozen) return;
    memset(osprey_run_table(run, OSPREY_TABLE_CENSUS_CHUNK), 0,
           (size_t)run->census_chunk_cap *
               table_record_size(OSPREY_TABLE_CENSUS_CHUNK));
    memset(osprey_run_table(run, OSPREY_TABLE_CENSUS_REGION), 0,
           (size_t)run->census_region_cap *
               table_record_size(OSPREY_TABLE_CENSUS_REGION));
    run->census_chunk_used = 0;
    run->census_region_used = 0;

    /* Re-insert the prefix chunks.  These are the same facts the census
     * was built from, so no limit can be exceeded by the rebuild. */
    OspreyRunIter it;
    const void *rec;
    const int tables[4] = {
        OSPREY_TABLE_PREFIX_ACCESS, OSPREY_TABLE_PREFIX_BASE,
        OSPREY_TABLE_PREFIX_COPY, OSPREY_TABLE_PREFIX_POINTS,
    };
    for (size_t t = 0; t < G_N_ELEMENTS(tables); t++) {
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = tables[t];
        while (osprey_run_iter_next(&it, &rec)) {
            const OspreyChunk *chunks[2] = { NULL, NULL };
            int n = 0;
            if (tables[t] == OSPREY_TABLE_PREFIX_ACCESS) {
                chunks[0] = &((const OspreyAccessFact *)rec)->chunk;
                n = 1;
            } else if (tables[t] == OSPREY_TABLE_PREFIX_BASE) {
                chunks[0] = &((const OspreyBaseFact *)rec)->chunk;
                n = 1;
            } else if (tables[t] == OSPREY_TABLE_PREFIX_COPY) {
                chunks[0] = &((const OspreyCopyFact *)rec)->source;
                chunks[1] = &((const OspreyCopyFact *)rec)->destination;
                n = 2;
            } else {
                chunks[0] = &((const OspreyPointsToFact *)rec)->pointer_chunk;
                n = 1;
            }
            for (int c = 0; c < n; c++) {
                OspreyCensusChunk cc;
                memset(&cc, 0, sizeof(cc));
                cc.chunk = *chunks[c];
                int rc = osprey_table_insert_census_chunk(run, &cc);
                if (rc == 1) {
                    OspreyCensusRegion cr;
                    memset(&cr, 0, sizeof(cr));
                    cr.region = chunks[c]->address.region;
                    cr.chunk_count = 1;
                    osprey_table_insert_census_region(run, &cr);
                }
            }
        }
    }
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
    ctx->logical_access_facts = g_array_new(FALSE, FALSE,
                                            sizeof(OspreyLogicalAccess));
    ctx->relations = NULL;
    ctx->runtime_regions = g_array_new(FALSE, FALSE, sizeof(OspreyRuntimeRegion));
    ctx->last_status = OSPREY_DISABLED;
    ctx->last_exact_logz = NAN;
    ctx->tx_status = OSPREY_DISABLED;
    ctx->tx_stage = NULL;
    ctx->tx_reason = NULL;
    ctx->tx_model_ready = false;
    ctx->analysis_started_us = -1;
    log_msg("[osprey] [config] [enabled %s] [analysis-mode %s] "
            "[work_limit %llu] [deadline_ms %llu] [parent_facts %llu] "
            "[parent_chunks %llu] [parent_regions %llu] "
            "[mutation_input %llu] [mutation_work %llu] [mutation_bytes %llu]\n",
            config->enabled ? "true" : "false",
            config->analysis_mode == OSPREY_ANALYSIS_MODE_MUTATION
                ? "mutation" : "full",
            (unsigned long long)config->max_analysis_work,
            (unsigned long long)config->analysis_deadline_ms,
            (unsigned long long)config->max_parent_facts,
            (unsigned long long)config->max_parent_chunks,
            (unsigned long long)config->max_parent_regions,
            (unsigned long long)config->max_mutation_input,
            (unsigned long long)config->max_mutation_work,
            (unsigned long long)config->max_mutation_bytes);
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
    osprey_runtime_index_clear(ctx);
    osprey_mutation_model_clear(ctx);
    g_array_free(ctx->region_instances, TRUE);
    g_array_free(ctx->logical_access_facts, TRUE);
    if (ctx->relations != NULL) {
        osprey_relations_free(ctx->relations);
    }
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

/* Supported OSPREY collection is single-threaded: CLONE_VM disables it
 * before guest threads resume.  Semantic helpers normally reuse one env;
 * cache that env, falling back to the table when CPUs switch.  Origin states
 * live until osprey_free_cpu_origins(), which clears this cache before
 * destroying them.  Forked samples inherit both the cache and its state;
 * resetting the shared fact suffix must preserve those pre-snapshot origins. */
static CPUArchState *g_cpu_origins_env = NULL;
static OspreyCpuOriginState *g_cpu_origins_state = NULL;

OspreyCpuOriginState *osprey_cpu_origin(CPUArchState *env) {
    if (g_cpu_origins_env == env && g_cpu_origins_state != NULL) {
        return g_cpu_origins_state;
    }
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
    g_cpu_origins_env = env;
    g_cpu_origins_state = st;
    return st;
}

void osprey_free_cpu_origins(void) {
    g_cpu_origins_env = NULL;
    g_cpu_origins_state = NULL;
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
