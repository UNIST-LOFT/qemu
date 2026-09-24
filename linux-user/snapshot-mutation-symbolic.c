/*
 * Bounded comparison-guided scalar mutation advisor (BinRadar only).
 *
 * This is symbolic *value synthesis*, not a solver.  It runs once in the
 * forkserver parent after the baseline patch-0 child exits, borrows the frozen
 * expression and query pools for the duration of the call, and owns nothing
 * afterwards.  See
 * agent-docs/done/plans/BINRADAR_IN_PROCESS_SYMBOLIC_MUTATION_PLAN.md.
 *
 * Pipeline:
 *  1. select eligible retained primitive reads in canonical baseline order;
 *  2. walk the frozen expression arena forward once, labelling each node that
 *     has exactly one labelled non-constant operand behind an invertible
 *     operation, and recording the observed value at every labelled node;
 *  3. scan the baseline query suffix once for branch comparisons whose one
 *     labelled operand is compared against a width-valid constant;
 *  4. generate the nearest value on the opposite side of the observed branch;
 *  5. invert the chain back to the load root, lower through the recorded root
 *     projection to the source width, and re-evaluate forward to prove the
 *     branch actually flips;
 *  6. rank deterministically, cap per source, and submit single-write
 *     OBSERVED_READ variants through the ordinary proposal sink.
 *
 * Every unsupported, malformed, or over-budget input is a local abstention:
 * the source keeps its generic alternatives and compact OSPREY keeps its
 * families.  Nothing here can remove or reorder an existing proposal.
 */

#include "qemu/osdep.h"
#include "snapshot-mutation-symbolic.h"

#include "../tcg/symbolic/symbolic-struct.h"

#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

/* ------------------------------------------------------------------ */
/* Configuration                                                       */
/* ------------------------------------------------------------------ */

#define SNAPSHOT_SYMBOLIC_DEFAULT_MAX_WORK 1000000ull
#define SNAPSHOT_SYMBOLIC_DEFAULT_MAX_BYTES (16ull * 1024ull * 1024ull)
#define SNAPSHOT_SYMBOLIC_DEFAULT_DEADLINE_MS 100ull

/* Test-only seams.  The focused runner includes this translation unit and can
 * drive these file-local controls without adding production API surface. */
static int64_t s_symbolic_test_alloc_fail_after = -1;
static bool s_symbolic_test_deadline_expired = false;

/* Advisor-owned allocation with the failure seam in front of it. */
static void *symbolic_try_malloc0(size_t bytes)
{
    if (s_symbolic_test_alloc_fail_after >= 0) {
        if (s_symbolic_test_alloc_fail_after == 0) return NULL;
        s_symbolic_test_alloc_fail_after--;
    }
    return g_try_malloc0(bytes);
}

/* Fixed ceilings.  The source ceiling is the retained primitive record count;
 * the label and table ceilings bound the sparse index regardless of guest
 * arena size, and both are charged against the byte budget before use. */
#define SNAPSHOT_SYMBOLIC_MAX_SOURCES MAX_PRIMITIVE_ACCESS
#define SNAPSHOT_SYMBOLIC_MAX_LABELS 65536u
#define SNAPSHOT_SYMBOLIC_TABLE_CAPACITY 131072u

typedef struct SnapshotSymbolicConfig {
    SnapshotSymbolicMode mode;
    uint64_t max_work;
    uint64_t max_bytes;
    uint64_t deadline_ms;
    bool valid;
} SnapshotSymbolicConfig;

static SnapshotSymbolicConfig s_symbolic_config = {
    .mode = SNAPSHOT_SYMBOLIC_OFF,
    .max_work = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_WORK,
    .max_bytes = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_BYTES,
    .deadline_ms = SNAPSHOT_SYMBOLIC_DEFAULT_DEADLINE_MS,
    .valid = false,
};

static bool parse_u64_env(const char *name, uint64_t *out)
{
    const char *text = getenv(name);
    char *end = NULL;
    unsigned long long value;

    if (text == NULL) return true; /* missing keeps the default */
    if (text[0] == '\0') return false;
    /* strtoull() accepts signs and leading whitespace.  The orchestrator's
     * contract is unsigned decimal digits only, so reject every other byte
     * before conversion instead of silently accepting a different language. */
    for (const char *cursor = text; *cursor != '\0'; cursor++) {
        if (*cursor < '0' || *cursor > '9') return false;
    }
    errno = 0;
    value = strtoull(text, &end, 10);
    if (end == text || (end != NULL && *end != '\0')) return false;
    if (errno == ERANGE && value == ULLONG_MAX) return false;
    *out = (uint64_t)value;
    return true;
}

/* Milliseconds to microseconds.  The guard adds the configured span to the
 * current monotonic clock, so the span itself must leave room for that sum;
 * clamping keeps the comparison in ``budget_expired`` from wrapping into a
 * deadline that has already passed. */
#define SNAPSHOT_SYMBOLIC_MAX_DEADLINE_MS \
    ((uint64_t)((INT64_MAX / 4) / 1000))

static uint64_t bounded_deadline_ms(uint64_t deadline_ms)
{
    return MIN(deadline_ms, SNAPSHOT_SYMBOLIC_MAX_DEADLINE_MS);
}

/* Absolute monotonic deadline in microseconds; zero disables the guard.  The
 * focused runner can force an already-expired guard so the deadline stop cause
 * is exercised deterministically instead of raced against the wall clock. */
static int64_t deadline_guard_us(uint64_t deadline_ms)
{
    uint64_t bounded = bounded_deadline_ms(deadline_ms);

    if (bounded == 0) return 0;
    if (s_symbolic_test_deadline_expired) {
        return g_get_monotonic_time() - 1000;
    }
    return g_get_monotonic_time() + (int64_t)(bounded * 1000ull);
}

void snapshot_symbolic_configure(void)
{
    static bool configured = false;
    const char *mode_text;
    SnapshotSymbolicConfig config;

    if (configured) return;
    configured = true;
    config = s_symbolic_config;

    mode_text = getenv("BINRADAR_SYMBOLIC_MUTATION_MODE");
    if (mode_text == NULL || mode_text[0] == '\0' ||
        strcmp(mode_text, "off") == 0) {
        config.mode = SNAPSHOT_SYMBOLIC_OFF;
    } else if (strcmp(mode_text, "shadow") == 0) {
        config.mode = SNAPSHOT_SYMBOLIC_SHADOW;
    } else if (strcmp(mode_text, "boundary") == 0) {
        config.mode = SNAPSHOT_SYMBOLIC_BOUNDARY;
    } else {
        /* Unknown mode text is a configuration failure.  Stay off rather than
         * guessing which behaviour the operator asked for. */
        log_msg("[symbolic-advisor] [config] [invalid-mode %s] [disabled]\n",
                mode_text);
        config.mode = SNAPSHOT_SYMBOLIC_OFF;
        config.valid = true;
        s_symbolic_config = config;
        return;
    }

    if (!parse_u64_env("BINRADAR_SYMBOLIC_MAX_WORK", &config.max_work) ||
        !parse_u64_env("BINRADAR_SYMBOLIC_MAX_BYTES", &config.max_bytes) ||
        !parse_u64_env("BINRADAR_SYMBOLIC_DEADLINE_MS", &config.deadline_ms)) {
        log_msg("[symbolic-advisor] [config] [invalid-number] [disabled]\n");
        config.mode = SNAPSHOT_SYMBOLIC_OFF;
    }
    if (config.max_work == 0) {
        config.max_work = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_WORK;
    }
    if (config.max_bytes == 0) {
        config.max_bytes = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_BYTES;
    }
    /* The `[config]` row reports the effective value, so a clamped deadline is
     * visible instead of silently truncated at use time. */
    config.deadline_ms = bounded_deadline_ms(config.deadline_ms);

    config.valid = true;
    s_symbolic_config = config;
    log_msg("[symbolic-advisor] [config] [mode %s] [max-work %llu] "
            "[max-bytes %llu] [deadline-ms %llu]\n",
            config.mode == SNAPSHOT_SYMBOLIC_BOUNDARY ? "boundary" :
            config.mode == SNAPSHOT_SYMBOLIC_SHADOW ? "shadow" : "off",
            (unsigned long long)config.max_work,
            (unsigned long long)config.max_bytes,
            (unsigned long long)config.deadline_ms);
}

SnapshotSymbolicMode snapshot_symbolic_mode(void)
{
    snapshot_symbolic_configure();
    return s_symbolic_config.mode;
}

/* ------------------------------------------------------------------ */
/* Bounded work, byte, and deadline accounting                         */
/* ------------------------------------------------------------------ */

typedef struct SnapshotSymbolicBudget {
    uint64_t max_work;
    uint64_t max_bytes;
    uint64_t work;
    uint64_t bytes;
    int64_t deadline_us;
    bool exhausted;
    bool work_exhausted;
    bool bytes_exhausted;
    bool deadline_exhausted;
} SnapshotSymbolicBudget;

static bool budget_charge_work(SnapshotSymbolicBudget *budget, uint64_t units)
{
    if (budget->exhausted) return false;
    if (units > budget->max_work - MIN(budget->work, budget->max_work)) {
        budget->work_exhausted = true;
        budget->exhausted = true;
        return false;
    }
    budget->work += units;
    return true;
}

/* Charge bytes *before* allocating.  The charged amount is the caller's
 * projected private footprint, so the advisor can never exceed the advertised
 * budget by allocating first and measuring later. */
static bool budget_reserve_bytes(SnapshotSymbolicBudget *budget, uint64_t bytes)
{
    if (budget->exhausted) return false;
    if (bytes > budget->max_bytes - MIN(budget->bytes, budget->max_bytes)) {
        budget->bytes_exhausted = true;
        budget->exhausted = true;
        return false;
    }
    budget->bytes += bytes;
    return true;
}

static bool budget_expired(const SnapshotSymbolicBudget *budget)
{
    return budget->deadline_us > 0 &&
           g_get_monotonic_time() >= budget->deadline_us;
}

/* Charge work and check the emergency deadline together.  The deadline is a
 * liveness guard, not the primary complexity bound. */
static bool budget_step(SnapshotSymbolicBudget *budget, uint64_t units)
{
    if (!budget_charge_work(budget, units)) return false;
    if (budget_expired(budget)) {
        budget->deadline_exhausted = true;
        budget->exhausted = true;
        return false;
    }
    return true;
}

/* ------------------------------------------------------------------ */
/* Fixed-width arithmetic and comparison                               */
/* ------------------------------------------------------------------ */

static uint64_t width_mask(uint8_t width)
{
    return width >= 8 ? UINT64_MAX : ((1ull << (8u * width)) - 1ull);
}

static uint64_t width_truncate(uint64_t value, uint8_t width)
{
    return value & width_mask(width);
}

/* Sign-extend from `width` bytes into the machine width. */
static uint64_t width_sign_extend(uint64_t value, uint8_t width)
{
    uint64_t sign;
    if (width >= 8) return value;
    sign = 1ull << (8u * width - 1u);
    return ((value & width_mask(width)) ^ sign) - sign;
}

static int64_t width_signed(uint64_t value, uint8_t width)
{
    return (int64_t)width_sign_extend(value, width);
}

static bool opkind_is_comparison(uint8_t opkind)
{
    switch ((OPKIND)opkind) {
    case EQ: case NE:
    case LT: case LE: case GE: case GT:
    case LTU: case LEU: case GEU: case GTU:
        return true;
    default:
        return false;
    }
}

/* Swap the sides of a comparison: (a OP b) <=> (b MIRROR(OP) a).  Returns 0
 * for anything that is not a comparison. */
static uint8_t mirror_opkind(uint8_t opkind)
{
    switch ((OPKIND)opkind) {
    case EQ: return EQ;
    case NE: return NE;
    case LT: return GT;
    case LE: return GE;
    case GE: return LE;
    case GT: return LT;
    case LTU: return GTU;
    case LEU: return GEU;
    case GEU: return LEU;
    case GTU: return LTU;
    default: return 0;
    }
}

/* Evaluate one recorded predicate at an exact width.  Signed comparisons
 * decode two's-complement at that width. */
static bool predicate_holds(uint8_t opkind, uint8_t width, uint64_t lhs,
                            uint64_t rhs)
{
    uint64_t l = width_truncate(lhs, width);
    uint64_t r = width_truncate(rhs, width);
    int64_t ls = width_signed(lhs, width);
    int64_t rs = width_signed(rhs, width);

    switch ((OPKIND)opkind) {
    case EQ: return l == r;
    case NE: return l != r;
    case LT: return ls < rs;
    case LE: return ls <= rs;
    case GE: return ls >= rs;
    case GT: return ls > rs;
    case LTU: return l < r;
    case LEU: return l <= r;
    case GEU: return l >= r;
    case GTU: return l > r;
    default: return false;
    }
}

/* The first representable value at `width` that makes the recorded satisfied
 * predicate false.  `exact` distinguishes the opposite boundary from an
 * adjacent exploratory value. */
static bool opposite_boundary(uint8_t opkind, uint8_t width, uint64_t observed,
                              uint64_t constant, uint64_t *out, bool *exact)
{
    uint64_t rhs = width_truncate(constant, width);
    uint64_t lhs = width_truncate(observed, width);
    int64_t rs = width_signed(constant, width);
    int64_t smin = (width >= 8) ? INT64_MIN
                                : -(int64_t)(1ull << (8u * width - 1u));
    int64_t smax = (width >= 8) ? INT64_MAX
                                : (int64_t)((1ull << (8u * width - 1u)) - 1ull);

    *exact = true;
    switch ((OPKIND)opkind) {
    case EQ:
        /* lhs == rhs held.  The constant is the boundary; step off it. */
        *out = width_truncate(rhs + 1u, width);
        if (*out == rhs) *out = width_truncate(rhs - 1u, width);
        *exact = false;
        return *out != lhs;
    case NE:
        /* lhs != rhs held; the constant itself satisfies the mirror. */
        *out = rhs;
        return *out != lhs;
    case LTU:
    case GTU:
        /* lhs < rhs / lhs > rhs: rhs is exactly on the far side. */
        *out = rhs;
        return *out != lhs;
    case LEU:
        /* At the maximum there is no value above rhs, so no false value
         * exists at this width. */
        if (rhs == width_mask(width)) {
            *exact = false;
            return false;
        }
        *out = width_truncate(rhs + 1u, width);
        return *out != lhs;
    case GEU:
        /* At zero there is no value below rhs, so no false value exists. */
        if (rhs == 0) {
            *exact = false;
            return false;
        }
        *out = width_truncate(rhs - 1u, width);
        return *out != lhs;
    case LT:
    case GT:
        *out = width_truncate((uint64_t)rs, width);
        return *out != lhs;
    case LE:
        if (rs >= smax) { *exact = false; return false; }
        *out = width_truncate((uint64_t)(rs + 1), width);
        return *out != lhs;
    case GE:
        if (rs <= smin) { *exact = false; return false; }
        *out = width_truncate((uint64_t)(rs - 1), width);
        return *out != lhs;
    default:
        return false;
    }
}

typedef struct SnapshotBoundaryValue {
    uint64_t value;
    uint8_t rank_class;
} SnapshotBoundaryValue;

static void boundary_append(uint8_t opkind, uint8_t width, uint64_t observed,
                            uint64_t constant, uint64_t value,
                            uint8_t rank_class, SnapshotBoundaryValue out[3],
                            uint32_t *count)
{
    value = width_truncate(value, width);
    if (value == width_truncate(observed, width) ||
        predicate_holds(opkind, width, value, constant)) {
        return;
    }
    for (uint32_t i = 0; i < *count; i++) {
        if (out[i].value == value) return;
    }
    if (*count < 3u) {
        out[*count].value = value;
        out[*count].rank_class = rank_class;
        (*count)++;
    }
}

/* Emit the exact opposite boundary plus representable neighbours that remain
 * on the opposite side.  Equality has no false exact boundary, so its two
 * representable neighbours are both adjacent candidates. */
static uint32_t boundary_values(uint8_t opkind, uint8_t width,
                                uint64_t observed, uint64_t constant,
                                SnapshotBoundaryValue out[3])
{
    uint64_t primary = 0;
    uint64_t mask = width_mask(width);
    bool exact = false;
    uint32_t count = 0;

    if (opkind == EQ) {
        uint64_t rhs = width_truncate(constant, width);
        if (rhs > 0) {
            boundary_append(opkind, width, observed, constant, rhs - 1u, 1,
                            out, &count);
        }
        if (rhs < mask) {
            boundary_append(opkind, width, observed, constant, rhs + 1u, 1,
                            out, &count);
        }
        return count;
    }
    if (!opposite_boundary(opkind, width, observed, constant,
                           &primary, &exact)) {
        return 0;
    }
    boundary_append(opkind, width, observed, constant, primary,
                    exact ? 0u : 1u, out, &count);

    if (opkind == LT || opkind == LE || opkind == GE || opkind == GT) {
        int64_t value = width_signed(primary, width);
        int64_t minimum = width >= 8
            ? INT64_MIN : -(int64_t)(1ull << (8u * width - 1u));
        int64_t maximum = width >= 8
            ? INT64_MAX : (int64_t)((1ull << (8u * width - 1u)) - 1u);
        if (value > minimum) {
            boundary_append(opkind, width, observed, constant,
                            (uint64_t)(value - 1), 1, out, &count);
        }
        if (value < maximum) {
            boundary_append(opkind, width, observed, constant,
                            (uint64_t)(value + 1), 1, out, &count);
        }
    } else {
        if (primary > 0) {
            boundary_append(opkind, width, observed, constant, primary - 1u,
                            1, out, &count);
        }
        if (primary < mask) {
            boundary_append(opkind, width, observed, constant, primary + 1u,
                            1, out, &count);
        }
    }
    return count;
}

/* ------------------------------------------------------------------ */
/* Labelled transform chain                                            */
/* ------------------------------------------------------------------ */

/* The root label is terminal (operand_index == -1) and carries the load's
 * machine-width projection of the recorded source bytes.  Inverting through it
 * is exactly the "lower to source width and check the projection image" step. */
typedef enum SnapshotSymbolicTransform {
    SNAPSHOT_SYMBOLIC_XFORM_ROOT_IDENTITY = 0,
    SNAPSHOT_SYMBOLIC_XFORM_ROOT_ZEXT = 1,
    SNAPSHOT_SYMBOLIC_XFORM_ROOT_SEXT = 2,
    SNAPSHOT_SYMBOLIC_XFORM_ZEXT = 3,
    SNAPSHOT_SYMBOLIC_XFORM_SEXT = 4,
    SNAPSHOT_SYMBOLIC_XFORM_ADD = 5,
    SNAPSHOT_SYMBOLIC_XFORM_SUB_POS = 6, /* node = operand - constant */
    SNAPSHOT_SYMBOLIC_XFORM_SUB_NEG = 7, /* node = constant - operand */
    SNAPSHOT_SYMBOLIC_XFORM_XOR = 8,
    SNAPSHOT_SYMBOLIC_XFORM_AND = 9,
} SnapshotSymbolicTransform;

static bool transform_is_root(uint8_t transform)
{
    return transform == SNAPSHOT_SYMBOLIC_XFORM_ROOT_IDENTITY ||
           transform == SNAPSHOT_SYMBOLIC_XFORM_ROOT_ZEXT ||
           transform == SNAPSHOT_SYMBOLIC_XFORM_ROOT_SEXT;
}

/* Apply the load's projection forward: source-width bytes -> machine width. */
static uint64_t root_project(uint8_t transform, uint64_t value,
                             uint8_t source_width)
{
    switch ((SnapshotSymbolicTransform)transform) {
    case SNAPSHOT_SYMBOLIC_XFORM_ROOT_ZEXT:
        return width_truncate(value, source_width);
    case SNAPSHOT_SYMBOLIC_XFORM_ROOT_SEXT:
        return width_sign_extend(value, source_width);
    default:
        return width_truncate(value, source_width);
    }
}

/* One labelled non-constant expression.  `result_width` is the byte width of
 * this node's value; `operand_width` is the byte width of the operand it was
 * derived from (equal except across ZEXT/SEXT). */
typedef struct SnapshotSymbolicLabel {
    int64_t operand_index;   /* -1 at the root */
    uint64_t constant;       /* transform constant, zero-extended */
    uint64_t observed;       /* forward value of this node under the baseline */
    uint32_t source_slot;
    uint8_t transform;
    uint8_t result_width;
    uint8_t operand_width;
    uint8_t reserved;
} SnapshotSymbolicLabel;

typedef struct SnapshotSymbolicIndex {
    int64_t *keys;
    uint32_t *values;        /* label id + 1; 0 means empty */
    uint32_t capacity;
    uint32_t count;
    SnapshotSymbolicLabel *labels;
    uint32_t label_count;
} SnapshotSymbolicIndex;

/* The keys table stores ``index + 1`` so that 0 stays a valid empty marker:
 * expression index 0 is a legal root and must not look like a free slot. */
static uint32_t table_hash(int64_t key, uint32_t mask)
{
    return (uint32_t)(((uint64_t)(key + 1) * 0x9E3779B97F4A7C15ull) >> 33) &
           mask;
}

static bool index_init(SnapshotSymbolicIndex *index,
                       SnapshotSymbolicBudget *budget)
{
    uint64_t table_bytes;
    uint64_t label_bytes;

    table_bytes = (uint64_t)SNAPSHOT_SYMBOLIC_TABLE_CAPACITY *
                  (sizeof(int64_t) + sizeof(uint32_t));
    label_bytes = (uint64_t)SNAPSHOT_SYMBOLIC_MAX_LABELS *
                  sizeof(SnapshotSymbolicLabel);
    if (!budget_reserve_bytes(budget, table_bytes + label_bytes)) return false;

    index->keys = symbolic_try_malloc0((size_t)table_bytes);
    if (index->keys == NULL) return false;
    index->values = (uint32_t *)(void *)((uint8_t *)index->keys +
        (uint64_t)SNAPSHOT_SYMBOLIC_TABLE_CAPACITY * sizeof(int64_t));
    index->labels = symbolic_try_malloc0((size_t)label_bytes);
    if (index->labels == NULL) {
        g_free(index->keys);
        index->keys = NULL;
        return false;
    }
    index->capacity = SNAPSHOT_SYMBOLIC_TABLE_CAPACITY;
    index->count = 0;
    index->label_count = 0;
    return true;
}

static void index_destroy(SnapshotSymbolicIndex *index)
{
    if (index == NULL) return;
    g_free(index->labels);
    g_free(index->keys);
    index->labels = NULL;
    index->keys = NULL;
}

/* Returns the label id, or UINT32_MAX when the expression carries none. */
static uint32_t index_lookup(const SnapshotSymbolicIndex *index, int64_t key)
{
    uint32_t slot;
    uint32_t mask;

    if (index == NULL || index->keys == NULL) return UINT32_MAX;
    mask = index->capacity - 1u;
    slot = table_hash(key, mask);
    for (uint32_t probe = 0; probe <= mask; probe++) {
        int64_t stored = index->keys[slot];
        if (stored == key + 1) return index->values[slot] - 1u;
        if (stored == 0) return UINT32_MAX;
        slot = (slot + 1u) & mask;
    }
    return UINT32_MAX;
}

/* Insert one key/label pair.  ``*cap_full`` distinguishes a bounded-capacity
 * refusal from a budget refusal so the caller can attribute each one. */
static bool index_insert(SnapshotSymbolicIndex *index, int64_t key,
                         uint32_t label, SnapshotSymbolicBudget *budget,
                         bool *cap_full)
{
    uint32_t mask;
    uint32_t slot;

    if (cap_full != NULL) *cap_full = false;
    if (index == NULL || index->keys == NULL) return false;
    mask = index->capacity - 1u;
    slot = table_hash(key, mask);
    for (uint32_t probe = 0; probe <= mask; probe++) {
        int64_t stored = index->keys[slot];
        if (stored == key + 1) {
            index->values[slot] = label + 1u;
            return true;
        }
        if (stored == 0) {
            if (!budget_charge_work(budget, 1)) return false;
            /* Keep a free slot so lookup termination stays bounded. */
            if (index->count + 1u >= index->capacity - (index->capacity >> 3)) {
                if (cap_full != NULL) *cap_full = true;
                return false;
            }
            index->keys[slot] = key + 1;
            index->values[slot] = label + 1u;
            index->count++;
            return true;
        }
        slot = (slot + 1u) & mask;
    }
    return false;
}

/* ------------------------------------------------------------------ */
/* Diagnostics                                                         */
/* ------------------------------------------------------------------ */

/* One measured pipeline stage.  `work` is the charged-work delta and `us` the
 * monotonic elapsed time, so a stage that is cheap in operations but slow in
 * wall time (or the reverse) is visible instead of being collapsed into the
 * aggregate budget counters. */
typedef enum SnapshotSymbolicStage {
    SNAPSHOT_SYMBOLIC_STAGE_ALLOC = 0,
    SNAPSHOT_SYMBOLIC_STAGE_INDEX = 1,
    SNAPSHOT_SYMBOLIC_STAGE_SOURCES = 2,
    SNAPSHOT_SYMBOLIC_STAGE_ROOTS = 3,
    SNAPSHOT_SYMBOLIC_STAGE_FORWARD = 4,
    SNAPSHOT_SYMBOLIC_STAGE_CONSUMERS = 5,
    SNAPSHOT_SYMBOLIC_STAGE_SUBMIT = 6,
    SNAPSHOT_SYMBOLIC_STAGE_COUNT = 7,
} SnapshotSymbolicStage;

/* First stage/reason that stopped the analysis.  `budget` deliberately stays
 * aggregate for existing consumers; this is the attribution P4a needs. */
typedef enum SnapshotSymbolicStop {
    SNAPSHOT_SYMBOLIC_STOP_NONE = 0,
    SNAPSHOT_SYMBOLIC_STOP_WORK = 1,
    SNAPSHOT_SYMBOLIC_STOP_BYTES = 2,
    SNAPSHOT_SYMBOLIC_STOP_DEADLINE = 3,
    SNAPSHOT_SYMBOLIC_STOP_ALLOCATION = 4,
    SNAPSHOT_SYMBOLIC_STOP_INDEX_CAP = 5,
    SNAPSHOT_SYMBOLIC_STOP_LABEL_CAP = 6,
    SNAPSHOT_SYMBOLIC_STOP_MALFORMED = 7,
} SnapshotSymbolicStop;

/* Bounded digest of the completed candidate set.  Field order is fixed by the
 * descriptor layout: source ordinal, width, canonical candidate rank, query
 * identity, lowered bytes.  Pointers, padding, wall time, and hash-table
 * insertion order are never hashed. */
#define SNAPSHOT_SYMBOLIC_DIGEST_ROUNDS 8u

typedef struct SnapshotSymbolicStats {
    uint32_t sources;
    uint32_t valid_roots;
    uint32_t consumers;
    uint32_t candidates;
    uint32_t candidates_generated;
    uint32_t families_generated;
    uint32_t families;
    uint32_t unsupported;
    uint32_t budget;
    uint64_t work;
    uint64_t bytes;
    int64_t start_us;
    int64_t end_us;
    /* P4a profiling */
    uint64_t stage_work[SNAPSHOT_SYMBOLIC_STAGE_COUNT];
    int64_t stage_us[SNAPSHOT_SYMBOLIC_STAGE_COUNT];
    uint32_t would_submit_families;
    uint32_t would_submit_variants;
    uint64_t digest[SNAPSHOT_SYMBOLIC_DIGEST_ROUNDS];
    bool digest_complete;
    bool analysis_complete;
    uint8_t stop_stage;
    uint8_t stop_reason;
    uint32_t allocation_failures;
    uint32_t index_cap_refusals;
    uint32_t label_cap_refusals;
    uint32_t submission_rejections;
} SnapshotSymbolicStats;

static bool detail_enabled(void)
{
    static int enabled = -1;
    if (enabled == -1) {
        const char *value = getenv("BINRADAR_SYMBOLIC_TEST_DETAIL");
        enabled = (value != NULL && strcmp(value, "1") == 0) ? 1 : 0;
    }
    return enabled == 1;
}

/* ------------------------------------------------------------------ */
/* Sources                                                             */
/* ------------------------------------------------------------------ */

typedef struct SnapshotSymbolicSource {
    uint32_t ordinal;        /* baseline entry ordinal */
    uint8_t width;           /* retained access width in bytes */
    uint8_t reserved[3];
    uint64_t observed;       /* observed source value, truncated to width */
    uint64_t addr;           /* retained access address */
} SnapshotSymbolicSource;

static bool source_is_eligible(const SnapshotMutationBaselineEntry *entry)
{
    if (entry == NULL) return false;
    if (!entry->typed_eligible || entry->protected_addr) return false;
    if (entry->lane != SNAPSHOT_MUTATION_LANE_PRIMITIVE) return false;
    if (entry->source_kind != SNAPSHOT_MUTATION_SOURCE_PRIMITIVE) return false;
    if (!entry->observed_read_valid) return false;
    if (entry->size != 1 && entry->size != 2 && entry->size != 4 &&
        entry->size != sizeof(target_ulong)) {
        return false;
    }
    if (entry->expr_index < 0 || entry->query_index < 0) return false;
    if (entry->root_extension > SNAPSHOT_ROOT_SEXT) return false;
    if (entry->addr < SNAPSHOT_PAGE_SIZE) return false;
    return snapshot_mutation_writable_span(entry->addr, entry->size);
}

/* ------------------------------------------------------------------ */
/* Candidates                                                          */
/* ------------------------------------------------------------------ */

typedef struct SnapshotSymbolicCandidate {
    uint32_t source_slot;
    uint32_t query_index;
    int64_t operand_index;   /* comparison operand carrying the label */
    uint64_t value;          /* required operand value at compare width */
    uint64_t lowered;        /* verified source-width value */
    uint64_t constant;       /* compare-width constant */
    uint64_t observed;       /* source-width observed value */
    uint8_t compare_width;   /* width the recorded predicate decides at */
    uint8_t rank_class;      /* 0 = exact opposite boundary, 1 = adjacent */
    uint8_t opkind;
    uint8_t reserved;
} SnapshotSymbolicCandidate;

static uint64_t distance_u64(uint64_t a, uint64_t b)
{
    return a >= b ? a - b : b - a;
}

static uint32_t popcount64(uint64_t value)
{
    uint32_t count = 0;
    while (value != 0) {
        value &= value - 1u;
        count++;
    }
    return count;
}

static int candidate_compare(const SnapshotSymbolicCandidate *a,
                             const SnapshotSymbolicCandidate *b)
{
    uint64_t da;
    uint64_t db;
    uint32_t ha;
    uint32_t hb;

    if (a->query_index != b->query_index) {
        return a->query_index < b->query_index ? -1 : 1;
    }
    if (a->rank_class != b->rank_class) {
        return a->rank_class < b->rank_class ? -1 : 1;
    }
    da = distance_u64(a->lowered, a->observed);
    db = distance_u64(b->lowered, b->observed);
    if (da != db) return da < db ? -1 : 1;
    ha = popcount64(a->lowered ^ a->observed);
    hb = popcount64(b->lowered ^ b->observed);
    if (ha != hb) return ha < hb ? -1 : 1;
    if (a->lowered != b->lowered) return a->lowered < b->lowered ? -1 : 1;
    return 0;
}

/* Primitive baseline entries are unique by address.  A fixed open-addressed
 * table makes wrapper-to-source binding O(1) expected work without allocating
 * from query cardinality or scanning all 4,096 sources for every query. */
#define SNAPSHOT_SYMBOLIC_SOURCE_TABLE_CAPACITY \
    (SNAPSHOT_SYMBOLIC_MAX_SOURCES * 2u)

typedef struct SnapshotSymbolicSourceLookupEntry {
    uint64_t addr;           /* zero is empty; eligible guest addresses are >= page */
    uint32_t slot_plus_one;
    uint32_t reserved;
} SnapshotSymbolicSourceLookupEntry;

/* ------------------------------------------------------------------ */
/* Engine                                                              */
/* ------------------------------------------------------------------ */

typedef struct SnapshotSymbolicEngine {
    const SnapshotSymbolicView *view;
    SnapshotSymbolicBudget budget;
    SnapshotSymbolicIndex index;
    SnapshotSymbolicSource *sources;
    SnapshotSymbolicSourceLookupEntry *source_lookup;
    SnapshotSymbolicCandidate *candidates;
    uint8_t *candidate_counts;
    uint32_t source_count;
    int64_t min_root_index;   /* smallest bound root, start of the forward pass */
    SnapshotSymbolicStats stats;
    bool aborted;
} SnapshotSymbolicEngine;

/* ------------------------------------------------------------------ */
/* Stage profiling                                                     */
/* ------------------------------------------------------------------ */

typedef struct SnapshotSymbolicStageMark {
    uint64_t work;
    int64_t start_us;
} SnapshotSymbolicStageMark;

static SnapshotSymbolicStageMark stage_begin(const SnapshotSymbolicEngine *engine)
{
    SnapshotSymbolicStageMark mark;

    mark.work = engine->budget.work;
    mark.start_us = g_get_monotonic_time();
    return mark;
}

/* Record one stage.  The first stop wins: a later stage that happens to touch
 * an already-exhausted budget must not relabel the real cause. */
static void stage_end(SnapshotSymbolicEngine *engine, SnapshotSymbolicStage stage,
                      SnapshotSymbolicStageMark mark)
{
    int64_t end_us = g_get_monotonic_time();

    engine->stats.stage_work[stage] = engine->budget.work - mark.work;
    engine->stats.stage_us[stage] += end_us - mark.start_us;
}

/* Attribute the stop to the stage that was running when it happened.  The
 * first stop wins: a later stage that happens to touch an already-exhausted
 * budget must not relabel the real cause. */
static void stage_abort(SnapshotSymbolicEngine *engine,
                        SnapshotSymbolicStage stage)
{
    SnapshotSymbolicStop reason = SNAPSHOT_SYMBOLIC_STOP_MALFORMED;

    if (engine->stats.stop_reason != SNAPSHOT_SYMBOLIC_STOP_NONE) return;
    if (engine->budget.work_exhausted) {
        reason = SNAPSHOT_SYMBOLIC_STOP_WORK;
    } else if (engine->budget.bytes_exhausted) {
        reason = SNAPSHOT_SYMBOLIC_STOP_BYTES;
    } else if (engine->budget.deadline_exhausted) {
        reason = SNAPSHOT_SYMBOLIC_STOP_DEADLINE;
    }
    engine->stats.stop_stage = (uint8_t)stage;
    engine->stats.stop_reason = (uint8_t)reason;
}

/* Allocation failure and fixed-capacity exhaustion are distinct from
 * unsupported expressions: the first two are environment/limit events, the
 * third is an ordinary grammar abstention. */
static void record_allocation_failure(SnapshotSymbolicEngine *engine,
                                      SnapshotSymbolicStage stage)
{
    engine->stats.allocation_failures++;
    if (engine->stats.stop_reason == SNAPSHOT_SYMBOLIC_STOP_NONE) {
        engine->stats.stop_stage = (uint8_t)stage;
        engine->stats.stop_reason = SNAPSHOT_SYMBOLIC_STOP_ALLOCATION;
    }
}

/* Called when a fixed table or label ceiling refuses an insertion.  When the
 * refusal ends the traversal (`aborted`) it is the stop; otherwise it is a
 * bounded-capacity abstention that the analysis survived. */
static void record_cap_refusal(SnapshotSymbolicEngine *engine,
                               SnapshotSymbolicStage stage,
                               SnapshotSymbolicStop reason)
{
    if (reason == SNAPSHOT_SYMBOLIC_STOP_LABEL_CAP) {
        engine->stats.label_cap_refusals++;
    } else {
        engine->stats.index_cap_refusals++;
    }
    if (!engine->aborted) return;
    if (engine->stats.stop_reason == SNAPSHOT_SYMBOLIC_STOP_NONE) {
        engine->stats.stop_stage = (uint8_t)stage;
        engine->stats.stop_reason = (uint8_t)reason;
    }
}

/* Mix one 64-bit word into the fixed digest state.  Independent of host
 * endianness and of any address the run happened to use. */
static void digest_mix(uint64_t digest[SNAPSHOT_SYMBOLIC_DIGEST_ROUNDS],
                       uint64_t value)
{
    for (uint32_t lane = 0; lane < SNAPSHOT_SYMBOLIC_DIGEST_ROUNDS; lane++) {
        uint64_t mixed = digest[lane] ^ value;
        mixed *= 0x9E3779B97F4A7C15ull;
        mixed ^= mixed >> 29;
        mixed *= 0xBF58476D1CE4E5B9ull;
        mixed ^= mixed >> 32;
        digest[lane] = mixed + (uint64_t)lane;
        value = mixed;
    }
}


static uint32_t source_hash(uint64_t addr)
{
    return (uint32_t)((addr * 0x9E3779B97F4A7C15ull) >> 32) &
           (SNAPSHOT_SYMBOLIC_SOURCE_TABLE_CAPACITY - 1u);
}

static bool source_lookup_insert(SnapshotSymbolicEngine *engine,
                                 uint32_t source_slot)
{
    const SnapshotSymbolicSource *source = &engine->sources[source_slot];
    uint32_t slot = source_hash(source->addr);

    for (uint32_t probe = 0;
         probe < SNAPSHOT_SYMBOLIC_SOURCE_TABLE_CAPACITY; probe++) {
        SnapshotSymbolicSourceLookupEntry *entry =
            &engine->source_lookup[slot];
        if (!budget_step(&engine->budget, 1)) {
            engine->aborted = true;
            return false;
        }
        if (entry->addr == 0) {
            entry->addr = source->addr;
            entry->slot_plus_one = source_slot + 1u;
            return true;
        }
        if (entry->addr == source->addr) {
            return true;
        }
        slot = (slot + 1u) &
               (SNAPSHOT_SYMBOLIC_SOURCE_TABLE_CAPACITY - 1u);
    }
    engine->aborted = true;
    return false;
}

static uint32_t source_lookup_find(SnapshotSymbolicEngine *engine,
                                   uint64_t addr)
{
    uint32_t slot = source_hash(addr);

    for (uint32_t probe = 0;
         probe < SNAPSHOT_SYMBOLIC_SOURCE_TABLE_CAPACITY; probe++) {
        const SnapshotSymbolicSourceLookupEntry *entry =
            &engine->source_lookup[slot];
        if (!budget_step(&engine->budget, 1)) {
            engine->aborted = true;
            return UINT32_MAX;
        }
        if (entry->addr == 0) return UINT32_MAX;
        if (entry->addr == addr) return entry->slot_plus_one - 1u;
        slot = (slot + 1u) &
               (SNAPSHOT_SYMBOLIC_SOURCE_TABLE_CAPACITY - 1u);
    }
    return UINT32_MAX;
}

static SnapshotSymbolicCandidate *engine_candidate_at(
    SnapshotSymbolicEngine *engine, uint32_t source_slot, uint32_t index)
{
    return &engine->candidates[
        (size_t)source_slot * SNAPSHOT_SYMBOLIC_MAX_CANDIDATES_PER_SOURCE +
        index];
}

/* Keep only the best three unique lowered source values.  Query order is the
 * primary rank, so an online bounded insertion is equivalent to sorting every
 * generated candidate and avoids candidate-count-dependent allocation. */
static bool engine_candidate_insert(SnapshotSymbolicEngine *engine,
                                    const SnapshotSymbolicCandidate *candidate)
{
    uint8_t *count = &engine->candidate_counts[candidate->source_slot];
    uint32_t position = *count;

    for (uint32_t i = 0; i < *count; i++) {
        SnapshotSymbolicCandidate *current =
            engine_candidate_at(engine, candidate->source_slot, i);
        if (!budget_step(&engine->budget, 1)) return false;
        if (current->lowered == candidate->lowered) return true;
        if (position == *count && candidate_compare(candidate, current) < 0) {
            position = i;
        }
    }
    if (*count == SNAPSHOT_SYMBOLIC_MAX_CANDIDATES_PER_SOURCE &&
        position == *count) {
        return true;
    }
    if (*count < SNAPSHOT_SYMBOLIC_MAX_CANDIDATES_PER_SOURCE) {
        (*count)++;
    }
    for (uint32_t i = *count - 1u; i > position; i--) {
        *engine_candidate_at(engine, candidate->source_slot, i) =
            *engine_candidate_at(engine, candidate->source_slot, i - 1u);
    }
    *engine_candidate_at(engine, candidate->source_slot, position) = *candidate;
    return true;
}

static const Expr *expr_at(const SnapshotSymbolicView *view, int64_t index)
{
    if (view == NULL || view->expr_base == NULL) return NULL;
    if (index < 0 || index >= view->expr_exit) return NULL;
    return &view->expr_base[index];
}

/* Follow an operand that must be an earlier non-constant expression in the
 * frozen arena.  Forward edges, cycles, out-of-window indexes, and invalid
 * constant tags all abstain.
 *
 * Every operand pointer is range-checked against the frozen window *before*
 * it is dereferenced.  This is not defensive: ZEXT/SEXT store their source
 * width directly in op2 without setting op2_is_const (see the load path in
 * symbolic.c), so an operand field can hold a small integer while its
 * *_is_const tag is clear.  Dereferencing first would fault on that operand. */
static bool expr_operand_index(const SnapshotSymbolicView *view,
                               const Expr *node, int operand,
                               bool operand_is_const, int64_t node_index,
                               int64_t *out_index)
{
    const Expr *operand_expr;
    int64_t index;

    if (node == NULL || out_index == NULL || operand_is_const) return false;
    switch (operand) {
    case 1: operand_expr = node->op1; break;
    case 2: operand_expr = node->op2; break;
    default: return false;
    }
    if (operand_expr == NULL || operand_expr < view->expr_base) return false;
    index = (int64_t)(operand_expr - view->expr_base);
    if (index < 0 || index >= view->expr_exit) return false;
    if (index >= node_index) return false; /* forward edge or cycle */
    if (operand_expr->opkind == IS_CONST) return false;
    *out_index = index;
    return true;
}

static bool engine_label(SnapshotSymbolicEngine *engine, int64_t index,
                         uint32_t source_slot, uint8_t transform,
                         uint64_t constant, uint8_t result_width,
                         uint8_t operand_width, int64_t operand_index,
                         uint64_t observed, SnapshotSymbolicStage stage)
{
    SnapshotSymbolicLabel *label;
    bool cap_full = false;

    if (engine->index.label_count >= SNAPSHOT_SYMBOLIC_MAX_LABELS) {
        engine->aborted = true;
        record_cap_refusal(engine, stage, SNAPSHOT_SYMBOLIC_STOP_LABEL_CAP);
        return false;
    }
    if (!budget_charge_work(&engine->budget, 1)) {
        engine->aborted = true;
        stage_abort(engine, stage);
        return false;
    }
    label = &engine->index.labels[engine->index.label_count];
    label->operand_index = operand_index;
    label->constant = constant;
    label->observed = observed;
    label->source_slot = source_slot;
    label->transform = transform;
    label->result_width = result_width;
    label->operand_width = operand_width;
    label->reserved = 0;
    if (!index_insert(&engine->index, index, engine->index.label_count,
                      &engine->budget, &cap_full)) {
        if (cap_full) {
            engine->aborted = true;
            record_cap_refusal(engine, stage,
                               SNAPSHOT_SYMBOLIC_STOP_INDEX_CAP);
        } else if (engine->budget.exhausted) {
            engine->aborted = true;
            stage_abort(engine, stage);
        }
        return false;
    }
    engine->index.label_count++;
    return true;
}

static bool engine_select_sources(SnapshotSymbolicEngine *engine)
{
    const SnapshotMutationBaseline *baseline = engine->view->baseline;

    if (baseline == NULL || baseline->entries == NULL) return false;
    /* Baseline entries are already in canonical order (primitive, then
     * pointer, then argument; each ordered by descending access id), so
     * iterating them directly keeps hash order out of source selection. */
    for (uint32_t ordinal = 0; ordinal < baseline->entry_count; ordinal++) {
        const SnapshotMutationBaselineEntry *entry =
            &baseline->entries[ordinal];
        SnapshotSymbolicSource *source;
        uint64_t observed = 0;

        if (engine->source_count >= SNAPSHOT_SYMBOLIC_MAX_SOURCES) break;
        if (!budget_step(&engine->budget, 1)) return false;
        if (!source_is_eligible(entry)) continue;
        memcpy(&observed, entry->observed_read_bytes, entry->size);
        source = &engine->sources[engine->source_count];
        source->ordinal = ordinal;
        source->width = (uint8_t)entry->size;
        source->observed = width_truncate(observed, source->width);
        source->addr = entry->addr;
        if (!source_lookup_insert(engine, engine->source_count)) return false;
        engine->source_count++;
        engine->stats.sources++;
    }
    return true;
}

/* Bytes copied into a concretization wrapper's constant operand, read back at
 * the wrapper's own width. */
static uint64_t wrapper_constant_bytes(const Expr *wrapper, uint8_t width)
{
    uint64_t value = 0;

    memcpy(&value, &wrapper->op2, width < sizeof(value) ? width
                                                        : sizeof(value));
    return width_truncate(value, width);
}

/* Classify a load root's machine-width projection from its shape.  The load
 * path builds a narrow load root as ZEXT/SEXT(source, 8*size) *without* setting
 * op2_is_const, so the source width is read from op2 directly, exactly as the
 * solver does.  `op3` carries the node's own width when the load was made at a
 * narrower type (a 32-bit load root records 4); a width outside the record is
 * not this advisor's shape and abstains.
 *
 * Returns false when the root is not a projection of `source_width` bytes. */
static bool root_projection(const Expr *root, uint8_t source_width,
                            uint8_t *transform_out, uint8_t *operand_width_out,
                            uint8_t *root_width_out)
{
    uint8_t root_width = (uint8_t)sizeof(target_ulong);
    uint8_t operand_width = (uint8_t)sizeof(target_ulong);
    uint8_t transform;

    if (root == NULL || transform_out == NULL || operand_width_out == NULL ||
        root_width_out == NULL) {
        return false;
    }
    if (root->op3_is_const) {
        uint64_t recorded = (uint64_t)CONST(root->op3);
        if (recorded > 0 && recorded <= sizeof(target_ulong)) {
            root_width = (uint8_t)recorded;
        }
    }
    if (root->opkind == ZEXT || root->opkind == SEXT) {
        uint64_t bits = (uint64_t)CONST(root->op2);
        if (bits == 0 || bits % 8u != 0 || bits > 64u) return false;
        operand_width = (uint8_t)(bits / 8u);
        transform = root->opkind == ZEXT ? SNAPSHOT_SYMBOLIC_XFORM_ROOT_ZEXT
                                         : SNAPSHOT_SYMBOLIC_XFORM_ROOT_SEXT;
    } else {
        /* A full-width load (or a 32-bit load whose value is already at its own
         * width) needs no projection: the root *is* the memory value. */
        transform = SNAPSHOT_SYMBOLIC_XFORM_ROOT_IDENTITY;
        operand_width = root_width;
    }
    if (operand_width != source_width || operand_width > root_width) {
        return false;
    }
    *transform_out = transform;
    *operand_width_out = operand_width;
    *root_width_out = root_width;
    return true;
}

/* Bind every retained source to the load roots that actually reached it.
 *
 * A retained primitive record is keyed by address, so a replacement keeps only
 * the *last* load of that address.  The branch under analysis may consume an
 * earlier load of the same bytes, whose root lives in the frozen prefix and can
 * never be reached from the replacement's root.  The child suffix's admitted
 * `BINRADAR_CONCRETIZATION` wrappers are the retained evidence for every load:
 * a wrapper whose copied address, width, and bytes match a retained record
 * proves that record's bytes flowed through that root.  Binding those aliases
 * is what makes the chain from the compared operand back to the memory cell
 * traversable at all.
 *
 * One wrapper may match at most one retained record (records are per address
 * and per lane, and only primitive lanes are eligible). */
static bool engine_bind_roots(SnapshotSymbolicEngine *engine)
{
    const SnapshotSymbolicView *view = engine->view;

    engine->min_root_index = view->expr_exit;
    for (int64_t qindex = view->query_entry; qindex < view->query_exit;
         qindex++) {
        const Query *query = &view->query_base[qindex];
        const Expr *wrapper = query->query;
        const Expr *root;
        int64_t wrapper_index;
        int64_t root_index;
        uint8_t width;
        uint64_t bytes;

        if (!budget_step(&engine->budget, 1)) return false;
        if (wrapper == NULL || wrapper->opkind != BINRADAR_CONCRETIZATION)
            continue;
        /* Rule 3: the wrapper itself must be in the child suffix. */
        if (wrapper < view->expr_base) continue;
        wrapper_index = (int64_t)(wrapper - view->expr_base);
        if (wrapper_index < view->expr_entry ||
            wrapper_index >= view->expr_exit) {
            continue;
        }
        if (!wrapper->op3_is_const || !wrapper->op2_is_const) continue;
        root = wrapper->op1;
        if (root == NULL || root->opkind == IS_CONST) continue;
        if (root < view->expr_base) continue;
        root_index = (int64_t)(root - view->expr_base);
        if (root_index < 0 || root_index >= wrapper_index) continue;
        width = (uint8_t)(uint64_t)CONST(wrapper->op3);
        if (width != 1 && width != 2 && width != 4 &&
            width != sizeof(target_ulong)) {
            continue;
        }
        bytes = wrapper_constant_bytes(wrapper, width);

        {
            uint32_t s = source_lookup_find(engine, query->address);
            const SnapshotSymbolicSource *source;
            const SnapshotMutationBaselineEntry *entry;
            uint8_t transform;
            uint8_t operand_width;
            uint8_t root_width;
            uint64_t projected;

            if (s == UINT32_MAX) {
                if (engine->aborted) return false;
                continue;
            }
            source = &engine->sources[s];
            entry = &view->baseline->entries[source->ordinal];
            if (source->width != width ||
                width_truncate(bytes, width) !=
                    width_truncate(source->observed, width)) {
                continue;
            }
            if (!root_projection(root, source->width, &transform,
                                 &operand_width, &root_width)) {
                engine->stats.unsupported++;
                continue;
            }
            /* The recorded extension is itself derived from the load's mem_op
             * at finalization, so for the record's own root the two
             * derivations must agree; a disagreement means the shape is not
             * the shape this advisor understands. */
            if (root_index == entry->expr_index &&
                transform != (uint8_t)(entry->root_extension ==
                                               SNAPSHOT_ROOT_ZEXT
                                           ? SNAPSHOT_SYMBOLIC_XFORM_ROOT_ZEXT
                                           : entry->root_extension ==
                                                     SNAPSHOT_ROOT_SEXT
                                                 ? SNAPSHOT_SYMBOLIC_XFORM_ROOT_SEXT
                                                 : SNAPSHOT_SYMBOLIC_XFORM_ROOT_IDENTITY)) {
                engine->stats.unsupported++;
                continue;
            }
            projected = width_truncate(
                root_project(transform, source->observed, operand_width),
                root_width);
            if (!engine_label(engine, root_index, s, transform, 0, root_width,
                              operand_width, -1, projected,
                              SNAPSHOT_SYMBOLIC_STAGE_ROOTS)) {
                if (engine->aborted) return false;
                engine->stats.unsupported++;
                continue;
            }
            if (root_index < engine->min_root_index) {
                engine->min_root_index = root_index;
            }
            engine->stats.valid_roots++;
        }
    }
    return true;
}

/* One forward pass over the frozen arena.  A node is labelled only when
 * exactly one non-constant operand carries a label and the operation is
 * supported and invertible. */
static bool engine_forward(SnapshotSymbolicEngine *engine)
{
    const SnapshotSymbolicView *view = engine->view;
    int64_t start = engine->min_root_index;

    if (start < 0 || start >= view->expr_exit) return true;

    /* Bound root labels are already in place; this pass only propagates them
     * forward through the supported transform grammar. */
    for (int64_t index = start; index < view->expr_exit; index++) {
        const Expr *node = expr_at(view, index);
        int64_t op1_index = -1, op2_index = -1;
        int64_t labelled_index = -1;
        uint32_t labelled_count = 0;
        uint32_t label_id;
        uint64_t observed;
        uint8_t result_width;
        bool labelled_is_op1;

        if (node == NULL) return false;
        if (!budget_step(&engine->budget, 1)) return false;
        if (index_lookup(&engine->index, index) != UINT32_MAX) continue;
        if (node->opkind == IS_CONST || node->opkind == IS_SYMBOLIC) continue;
        if (expr_operand_index(view, node, 1, node->op1_is_const, index,
                               &op1_index) &&
            index_lookup(&engine->index, op1_index) != UINT32_MAX) {
            labelled_count++;
            labelled_index = op1_index;
        }
        if (expr_operand_index(view, node, 2, node->op2_is_const, index,
                               &op2_index) &&
            index_lookup(&engine->index, op2_index) != UINT32_MAX) {
            labelled_count++;
            labelled_index = op2_index;
        }
        if (labelled_count != 1) {
            if (labelled_count > 1) engine->stats.unsupported++;
            continue;
        }
        if (!budget_step(&engine->budget, 1)) return false;

        label_id = index_lookup(&engine->index, labelled_index);
        observed = engine->index.labels[label_id].observed;
        result_width = engine->index.labels[label_id].result_width;
        /* Only the operand orientation matters for arithmetic; the labelled
         * operand is op1 or op2 by construction of labelled_index. */
        labelled_is_op1 = (labelled_index == op1_index);

        switch ((OPKIND)node->opkind) {
        case ZEXT:
        case SEXT: {
            uint64_t bits;
            uint8_t from_width;
            uint64_t extended;
            /* ZEXT/SEXT always carry their source width in op2; the solver
             * reads it as a constant unconditionally (solver/main.c), and the
             * load path that builds the root does not set op2_is_const. */
            if (!labelled_is_op1) {
                engine->stats.unsupported++;
                break;
            }
            bits = (uint64_t)CONST(node->op2);
            if (bits == 0 || bits % 8u != 0 || bits > 64u) {
                engine->stats.unsupported++;
                break;
            }
            from_width = (uint8_t)(bits / 8u);
            if (from_width > result_width) {
                engine->stats.unsupported++;
                break;
            }
            extended = node->opkind == ZEXT
                ? width_truncate(observed, from_width)
                : width_sign_extend(observed, from_width);
            if (!engine_label(engine, index,
                              engine->index.labels[label_id].source_slot,
                              node->opkind == ZEXT
                                  ? SNAPSHOT_SYMBOLIC_XFORM_ZEXT
                                  : SNAPSHOT_SYMBOLIC_XFORM_SEXT,
                              0, (uint8_t)sizeof(target_ulong), from_width,
                              labelled_index, extended,
                              SNAPSHOT_SYMBOLIC_STAGE_FORWARD)) {
                return false;
            }
            break;
        }
        case ADD:
        case SUB:
        case XOR:
        case AND: {
            int constant_operand = labelled_is_op1 ? 2 : 1;
            bool constant_is_const = constant_operand == 2
                ? node->op2_is_const : node->op1_is_const;
            uint64_t constant;
            uint64_t operand_value;
            uint64_t result;
            uint8_t transform;
            uint8_t op_width = result_width;

            /* An i32 operation records its width in op3 (the i64 case leaves
             * it zero).  The solver resizes both operands to that width, so
             * the operation is genuinely truncated there and the labelled
             * value reaching this node must be truncated too. */
            if (node->op3_is_const) {
                uint64_t recorded = (uint64_t)CONST(node->op3);
                if (recorded == 0) {
                    op_width = sizeof(target_ulong);
                } else if (recorded <= sizeof(target_ulong)) {
                    op_width = (uint8_t)recorded;
                } else {
                    engine->stats.unsupported++;
                    break;
                }
            }
            if (op_width > result_width) {
                /* Widening cannot be justified without a projection. */
                engine->stats.unsupported++;
                break;
            }
            /* AND with a constant has a second, unlabelled operand that is
             * still fully determined, so it is invertible.  The other three
             * need the constant to be the non-labelled side. */
            if (!constant_is_const) {
                engine->stats.unsupported++;
                break;
            }
            operand_value = width_truncate(observed, op_width);
            constant = width_truncate(
                (uint64_t)CONST(constant_operand == 2 ? node->op2
                                                      : node->op1),
                op_width);
            switch ((OPKIND)node->opkind) {
            case ADD:
                transform = SNAPSHOT_SYMBOLIC_XFORM_ADD;
                result = operand_value + constant;
                break;
            case SUB:
                transform = labelled_is_op1 ? SNAPSHOT_SYMBOLIC_XFORM_SUB_POS
                                            : SNAPSHOT_SYMBOLIC_XFORM_SUB_NEG;
                result = labelled_is_op1 ? operand_value - constant
                                         : constant - operand_value;
                break;
            case XOR:
                transform = SNAPSHOT_SYMBOLIC_XFORM_XOR;
                result = operand_value ^ constant;
                break;
            default:
                transform = SNAPSHOT_SYMBOLIC_XFORM_AND;
                result = operand_value & constant;
                break;
            }
            if (!engine_label(engine, index,
                              engine->index.labels[label_id].source_slot,
                              transform, constant, op_width,
                              op_width, labelled_index,
                              width_truncate(result, op_width),
                              SNAPSHOT_SYMBOLIC_STAGE_FORWARD)) {
                return false;
            }
            break;
        }
        default:
            engine->stats.unsupported++;
            break;
        }
    }
    return true;
}

/* Invert the chain from the comparison operand back to the load root.  On
 * success `*source_out` holds the required source-width bytes.  Any step whose
 * requested value lies outside its projection image fails the inversion. */
static bool engine_invert(SnapshotSymbolicEngine *engine,
                          int64_t operand_index, uint64_t required,
                          uint64_t *source_out)
{
    const SnapshotSymbolicIndex *index = &engine->index;
    int64_t cursor = operand_index;
    uint32_t guard = 0;

    while (cursor >= 0 && guard++ <= index->label_count) {
        uint32_t label_id;

        if (!budget_step(&engine->budget, 1)) return false;
        label_id = index_lookup(index, cursor);
        const SnapshotSymbolicLabel *label;
        uint64_t mask;

        if (label_id == UINT32_MAX) return false;
        label = &index->labels[label_id];
        if (transform_is_root(label->transform)) {
            /* The root projects source-width bytes into the machine width.
             * Invert by checking the image and truncating. */
            switch ((SnapshotSymbolicTransform)label->transform) {
            case SNAPSHOT_SYMBOLIC_XFORM_ROOT_ZEXT:
                if (label->operand_width < 8 &&
                    (required >> (8u * label->operand_width)) != 0) {
                    return false;
                }
                break;
            case SNAPSHOT_SYMBOLIC_XFORM_ROOT_SEXT:
                if (label->operand_width < 8 &&
                    width_sign_extend(required, label->operand_width) !=
                        width_truncate(required,
                                       (uint8_t)sizeof(target_ulong))) {
                    return false;
                }
                break;
            default:
                break;
            }
            *source_out = width_truncate(required, label->operand_width);
            return true;
        }
        switch ((SnapshotSymbolicTransform)label->transform) {
        case SNAPSHOT_SYMBOLIC_XFORM_ZEXT:
            /* Zero-extension image: the upper bits must already be zero, and
             * the operand is exactly the low bits. */
            if (label->operand_width < 8 &&
                (required >> (8u * label->operand_width)) != 0) {
                return false;
            }
            required = width_truncate(required, label->operand_width);
            break;
        case SNAPSHOT_SYMBOLIC_XFORM_SEXT:
            /* Sign-extension image: the upper bits must equal the sign bit,
             * and the operand is exactly the low bits. */
            if (label->operand_width < 8 &&
                width_sign_extend(required, label->operand_width) !=
                    width_truncate(required, (uint8_t)sizeof(target_ulong))) {
                return false;
            }
            required = width_truncate(required, label->operand_width);
            break;
        case SNAPSHOT_SYMBOLIC_XFORM_ADD:
            required = width_truncate(required - label->constant,
                                      label->result_width);
            break;
        case SNAPSHOT_SYMBOLIC_XFORM_SUB_POS:
            required = width_truncate(required + label->constant,
                                      label->result_width);
            break;
        case SNAPSHOT_SYMBOLIC_XFORM_SUB_NEG:
            required = width_truncate(label->constant - required,
                                      label->result_width);
            break;
        case SNAPSHOT_SYMBOLIC_XFORM_XOR:
            required = width_truncate(required ^ label->constant,
                                      label->result_width);
            break;
        case SNAPSHOT_SYMBOLIC_XFORM_AND:
            mask = width_mask(label->result_width);
            /* A preimage exists only when the requested target keeps no bit
             * outside the mask; unconstrained bits are copied from the
             * observed value so the candidate stays as close as possible. */
            if ((required & ~label->constant & mask) != 0) {
                return false;
            }
            required = width_truncate(
                (required & label->constant) |
                    (label->observed & ~label->constant & mask),
                label->result_width);
            break;
        default:
            return false;
        }
        cursor = label->operand_index;
    }
    return false;
}

/* Re-evaluate the chain forward from the source bytes and report whether the
 * recorded predicate becomes false. */
static bool engine_reevaluate(SnapshotSymbolicEngine *engine,
                              const SnapshotSymbolicCandidate *candidate,
                              uint64_t source_value)
{
    const SnapshotSymbolicIndex *index = &engine->index;
    uint64_t chain[64];
    uint32_t count = 0;
    int64_t cursor = candidate->operand_index;
    uint64_t value;

    /* Collect the chain outward-in: operand, its operand, ... root. */
    while (cursor >= 0 && count < G_N_ELEMENTS(chain)) {
        uint32_t label_id;

        if (!budget_step(&engine->budget, 1)) return false;
        label_id = index_lookup(index, cursor);
        if (label_id == UINT32_MAX) return false;
        chain[count++] = label_id;
        cursor = index->labels[label_id].operand_index;
    }
    if (count == 0 || count > G_N_ELEMENTS(chain)) return false;
    if (!transform_is_root(
            index->labels[(uint32_t)chain[count - 1]].transform)) {
        return false;
    }

    /* chain[count-1] is the root: project the source-width candidate value
     * into the machine width exactly as the load did. */
    value = root_project(index->labels[(uint32_t)chain[count - 1]].transform,
                         source_value,
                         index->labels[(uint32_t)chain[count - 1]]
                             .operand_width);
    for (int32_t i = (int32_t)count - 2; i >= 0; i--) {
        const SnapshotSymbolicLabel *label =
            &index->labels[(uint32_t)chain[i]];
        if (!budget_step(&engine->budget, 1)) return false;
        switch ((SnapshotSymbolicTransform)label->transform) {
        case SNAPSHOT_SYMBOLIC_XFORM_ZEXT:
            /* The extension reads only the low operand_width bytes. */
            value = width_truncate(value, label->operand_width);
            break;
        case SNAPSHOT_SYMBOLIC_XFORM_SEXT:
            value = width_sign_extend(value, label->operand_width);
            break;
        case SNAPSHOT_SYMBOLIC_XFORM_ADD:
            value = value + label->constant;
            break;
        case SNAPSHOT_SYMBOLIC_XFORM_SUB_POS:
            value = value - label->constant;
            break;
        case SNAPSHOT_SYMBOLIC_XFORM_SUB_NEG:
            value = label->constant - value;
            break;
        case SNAPSHOT_SYMBOLIC_XFORM_XOR:
            value = value ^ label->constant;
            break;
        case SNAPSHOT_SYMBOLIC_XFORM_AND:
            value = value & label->constant;
            break;
        default:
            return false;
        }
    }
    /* Mirror the solver's comparison resize, then evaluate the recorded
     * predicate.  The candidate is useful only when it no longer holds. */
    return !predicate_holds(candidate->opkind, candidate->compare_width, value,
                            candidate->constant);
}

/* One pass over the baseline query suffix.  The recorded predicate is the one
 * the baseline satisfied; a candidate is useful when it makes that predicate
 * false.  Comparison width follows the solver: EQ/NE decide at op3 bytes,
 * relational operators resize both operands to their common width, which is
 * the machine width for any chain the load produced. */
static bool engine_consumers(SnapshotSymbolicEngine *engine)
{
    const SnapshotSymbolicView *view = engine->view;

    for (int64_t qindex = view->query_entry; qindex < view->query_exit;
         qindex++) {
        const Query *query = &view->query_base[qindex];
        const Expr *branch = query->query;
        int64_t branch_index;
        int64_t op1_index = -1, op2_index = -1;
        int64_t labelled_index = -1;
        uint32_t labelled_count = 0;
        uint8_t compare_width;
        uint8_t operand_width;
        uint64_t constant;
        uint64_t observed;
        uint32_t source_slot;
        uint32_t label_id;
        uint64_t mask;
        uint8_t opkind;
        SnapshotBoundaryValue boundaries[3];
        uint32_t boundary_count;

        if (!budget_step(&engine->budget, 1)) return false;
        if (branch == NULL || branch->opkind == IS_CONST) continue;
        if (branch < view->expr_base) continue;
        branch_index = (int64_t)(branch - view->expr_base);
        if (branch_index < 0 || branch_index >= view->expr_exit) continue;
        if (!opkind_is_comparison(branch->opkind)) continue;
        if (branch->opkind == EQ || branch->opkind == NE) {
            compare_width = (uint8_t)CONST(branch->op3);
            if (compare_width == 0) compare_width = sizeof(target_ulong);
        } else {
            /* Relational operators resize both operands to their common width,
             * which the solver takes as the machine width; the constant is
             * built at machine width, so the predicate decides there. */
            compare_width = sizeof(target_ulong);
        }
        if (compare_width != 1 && compare_width != 2 && compare_width != 4 &&
            compare_width != sizeof(target_ulong)) {
            engine->stats.unsupported++;
            continue;
        }

        /* Exactly one operand is a labelled expression, the other a constant. */
        if (expr_operand_index(view, branch, 1, branch->op1_is_const,
                               branch_index, &op1_index) &&
            index_lookup(&engine->index, op1_index) != UINT32_MAX) {
            labelled_count++;
            labelled_index = op1_index;
        }
        if (expr_operand_index(view, branch, 2, branch->op2_is_const,
                               branch_index, &op2_index) &&
            index_lookup(&engine->index, op2_index) != UINT32_MAX) {
            labelled_count++;
            labelled_index = op2_index;
        }
        if (labelled_count != 1) {
            if (labelled_count > 1) engine->stats.unsupported++;
            continue;
        }
        if (labelled_index == op1_index) {
            if (!branch->op2_is_const) continue;
            constant = (uint64_t)CONST(branch->op2);
            opkind = branch->opkind;
        } else {
            if (!branch->op1_is_const) continue;
            constant = (uint64_t)CONST(branch->op1);
            /* The recorded shape is (constant OP labelled).  Mirror the
             * operator so the predicate is always read with the labelled
             * value on the left, which the boundary and verify steps assume. */
            opkind = mirror_opkind(branch->opkind);
            if (opkind == 0) {
                engine->stats.unsupported++;
                continue;
            }
        }
        label_id = index_lookup(&engine->index, labelled_index);
        source_slot = engine->index.labels[label_id].source_slot;
        if (source_slot >= engine->source_count) continue;
        operand_width = engine->index.labels[label_id].result_width;
        /* The solver resizes both comparison operands to the comparison width
         * by zero-extension, so a narrower labelled operand is exact at the
         * wider comparison.  Truncation (a wider operand) is not modelled and
         * abstains. */
        if (compare_width < operand_width) {
            engine->stats.unsupported++;
            continue;
        }
        engine->stats.consumers++;

        observed = width_truncate(engine->index.labels[label_id].observed,
                                  compare_width);
        /* Self-validation: the baseline satisfied the recorded predicate, so
         * the operand value reconstructed from the observed source bytes must
         * satisfy it too at the comparison width.  A disagreement means the
         * chain or the width does not model this branch, which is an
         * abstention rather than a guess. */
        if (!predicate_holds(opkind, compare_width, observed, constant)) {
            engine->stats.unsupported++;
            continue;
        }
        boundary_count = boundary_values(opkind, compare_width, observed,
                                         constant, boundaries);
        if (boundary_count == 0) {
            engine->stats.unsupported++;
            continue;
        }
        mask = width_mask(compare_width);
        for (uint32_t bi = 0; bi < boundary_count; bi++) {
            const SnapshotSymbolicSource *source =
                &engine->sources[source_slot];
            const SnapshotMutationBaselineEntry *entry =
                &view->baseline->entries[source->ordinal];
            SnapshotSymbolicCandidate candidate;
            uint64_t operand_value;
            uint64_t lowered = 0;

            if (!budget_step(&engine->budget, 1)) return false;
            /* Bits outside the comparison width are free; copy them from the
             * observed operand so the candidate stays as close as possible. */
            operand_value =
                (engine->index.labels[label_id].observed & ~mask) |
                (boundaries[bi].value & mask);
            memset(&candidate, 0, sizeof(candidate));
            candidate.source_slot = source_slot;
            candidate.query_index = (uint32_t)qindex;
            candidate.operand_index = labelled_index;
            candidate.value = operand_value;
            candidate.constant = width_truncate(constant, compare_width);
            candidate.observed = source->observed;
            candidate.compare_width = compare_width;
            candidate.rank_class = boundaries[bi].rank_class;
            candidate.opkind = opkind;
            engine->stats.candidates++;

            if (!engine_invert(engine, candidate.operand_index,
                               candidate.value, &lowered)) {
                if (engine->budget.exhausted) return false;
                engine->stats.unsupported++;
                continue;
            }
            candidate.lowered = lowered;
            if (!engine_reevaluate(engine, &candidate, lowered)) {
                if (engine->budget.exhausted) return false;
                continue;
            }
            if (lowered == source->observed ||
                memcmp(&lowered, entry->planner_bytes, source->width) == 0) {
                continue;
            }
            engine->stats.candidates_generated++;
            if (!engine_candidate_insert(engine, &candidate)) return false;
        }
    }
    return true;
}

/* ------------------------------------------------------------------ */
/* Submission                                                          */
/* ------------------------------------------------------------------ */

/* Outcome of one family submission.  An advisor-owned allocation failure is
 * an environment event and must not be reported as a sink rejection (quota or
 * validation), which is an ordinary local abstention. */
typedef enum SnapshotSymbolicSubmitResult {
    SNAPSHOT_SYMBOLIC_SUBMIT_DONE = 0,       /* nothing left to publish */
    SNAPSHOT_SYMBOLIC_SUBMIT_REJECTED = 1,   /* sink refused the family */
    SNAPSHOT_SYMBOLIC_SUBMIT_ALLOCATION = 2, /* advisor ran out of memory */
} SnapshotSymbolicSubmitResult;

/* Verify and submit the best candidates for one source.  A candidate is only
 * submitted when the independent forward re-evaluation proves the recorded
 * predicate flips, when the lowered value is in the root projection's image,
 * and when it differs from both the physical and observed baseline bytes.
 *
 * ``*emitted_out`` reports how many variants survived verification: zero means
 * every candidate was a local abstention and nothing was proposed, which the
 * caller must not count as a submitted family. */
static SnapshotSymbolicSubmitResult submit_source(
                          SnapshotSymbolicEngine *engine,
                          SnapshotMutationProposalSink *sink,
                          const SnapshotSymbolicCandidate **selected,
                          uint32_t count, uint32_t source_slot,
                          uint32_t *emitted_out)
{
    const SnapshotSymbolicSource *source = &engine->sources[source_slot];
    const SnapshotMutationBaselineEntry *entry =
        &engine->view->baseline->entries[source->ordinal];
    SnapshotMutationProposalFamily family;
    SnapshotMutationProposalVariant *variants;
    SnapshotMutationProposalWrite *writes;
    uint32_t emitted = 0;
    bool ok;

    *emitted_out = 0;
    if (count == 0) return SNAPSHOT_SYMBOLIC_SUBMIT_DONE;
    variants = symbolic_try_malloc0((size_t)count * sizeof(*variants));
    if (variants == NULL) return SNAPSHOT_SYMBOLIC_SUBMIT_ALLOCATION;
    writes = symbolic_try_malloc0((size_t)count * sizeof(*writes));
    if (writes == NULL) {
        g_free(variants);
        return SNAPSHOT_SYMBOLIC_SUBMIT_ALLOCATION;
    }
    memset(&family, 0, sizeof(family));
    family.advisor_id = SNAPSHOT_SYMBOLIC_ADVISOR_ID;
    family.advisor_priority = SNAPSHOT_SYMBOLIC_ADVISOR_PRIORITY;
    family.family_id = source->ordinal;
    family.primary_seed = entry->token;
    family.seed_semantics = SNAPSHOT_MUTATION_SEED_OBSERVED_READ;

    for (uint32_t i = 0; i < count; i++) {
        const SnapshotSymbolicCandidate *candidate = selected[i];
        uint64_t lowered = candidate->lowered;

        writes[emitted].destination = entry->token;
        writes[emitted].kind = SNAPSHOT_MUTATION_BYTES;
        writes[emitted].size = source->width;
        memcpy(writes[emitted].value, &lowered, sizeof(writes[emitted].value));
        variants[emitted].variant_id = emitted;
        variants[emitted].write_count = 1;
        variants[emitted].writes = &writes[emitted];
        if (detail_enabled()) {
            log_msg("[symbolic-advisor] [detail] [source %u] [ordinal %u] "
                    "[query %u] [width %u] [opkind %u] [value %llx] "
                    "[observed %llx] [constant %llx] [exact %u]\n",
                    source_slot, source->ordinal, candidate->query_index,
                    candidate->compare_width, candidate->opkind,
                    (unsigned long long)lowered,
                    (unsigned long long)source->observed,
                    (unsigned long long)candidate->constant,
                    candidate->rank_class == 0 ? 1u : 0u);
        }
        emitted++;
    }
    if (emitted == 0) {
        g_free(writes);
        g_free(variants);
        return SNAPSHOT_SYMBOLIC_SUBMIT_DONE;
    }
    *emitted_out = emitted;
    family.variant_count = emitted;
    family.variants = variants;
    ok = snapshot_mutation_sink_submit(sink, &family);
    g_free(writes);
    g_free(variants);
    /* A false return is the sink's own rejection (quota or validation), not
     * an advisor allocation failure: the two are counted separately. */
    return ok ? SNAPSHOT_SYMBOLIC_SUBMIT_DONE
              : SNAPSHOT_SYMBOLIC_SUBMIT_REJECTED;
}

/* Summarize a *completed* analysis: the would-submit family count and a
 * deterministic digest over the fixed candidate slots in canonical
 * source/rank order.
 *
 * Shadow mode never reaches the sink, so its `families-generated`/
 * `families-accepted` counters stay zero by contract; `would-submit-*` is the
 * estimate of what boundary mode would have proposed for the same frozen
 * arena.  Candidate slots are already ranked (query, class, distance, Hamming,
 * value), so hashing them in slot order is order-stable. */
static void summarize_completed_analysis(SnapshotSymbolicEngine *engine)
{
    uint32_t families = 0;
    uint32_t variants = 0;

    for (uint32_t s = 0; s < engine->source_count; s++) {
        const SnapshotSymbolicSource *source = &engine->sources[s];
        uint32_t count = engine->candidate_counts[s];

        digest_mix(engine->stats.digest, source->ordinal);
        digest_mix(engine->stats.digest, source->width);
        digest_mix(engine->stats.digest, count);
        if (count > 0) {
            families++;
            variants += count;
        }
        for (uint32_t ci = 0; ci < count; ci++) {
            const SnapshotSymbolicCandidate *candidate =
                engine_candidate_at(engine, s, ci);

            /* Identity of the descriptor: rank position, the recorded query
             * it came from, the compare shape, and the lowered bytes that
             * would be written.  Never an address or a pointer. */
            digest_mix(engine->stats.digest, ci);
            digest_mix(engine->stats.digest, candidate->query_index);
            digest_mix(engine->stats.digest, candidate->compare_width);
            digest_mix(engine->stats.digest, candidate->opkind);
            digest_mix(engine->stats.digest, candidate->rank_class);
            digest_mix(engine->stats.digest, candidate->lowered);
            digest_mix(engine->stats.digest, candidate->constant);
            digest_mix(engine->stats.digest, candidate->observed);
        }
    }
    engine->stats.would_submit_families = families;
    engine->stats.would_submit_variants = variants;
    engine->stats.digest_complete = true;
}

/* Last completed-or-aborted profile, retained so the focused runner can assert
 * the digest and stop attribution without parsing the log.  One fixed copy per
 * analysis run (not per load, plan, or candidate). */
static SnapshotSymbolicStats s_symbolic_last_stats;

static const char *stage_name(SnapshotSymbolicStage stage)
{
    switch (stage) {
    case SNAPSHOT_SYMBOLIC_STAGE_ALLOC: return "alloc";
    case SNAPSHOT_SYMBOLIC_STAGE_INDEX: return "index";
    case SNAPSHOT_SYMBOLIC_STAGE_SOURCES: return "sources";
    case SNAPSHOT_SYMBOLIC_STAGE_ROOTS: return "roots";
    case SNAPSHOT_SYMBOLIC_STAGE_FORWARD: return "forward";
    case SNAPSHOT_SYMBOLIC_STAGE_CONSUMERS: return "consumers";
    case SNAPSHOT_SYMBOLIC_STAGE_SUBMIT: return "submit";
    default: return "none";
    }
}

static const char *stop_reason_name(SnapshotSymbolicStop reason)
{
    switch (reason) {
    case SNAPSHOT_SYMBOLIC_STOP_WORK: return "work";
    case SNAPSHOT_SYMBOLIC_STOP_BYTES: return "bytes";
    case SNAPSHOT_SYMBOLIC_STOP_DEADLINE: return "deadline";
    case SNAPSHOT_SYMBOLIC_STOP_ALLOCATION: return "allocation";
    case SNAPSHOT_SYMBOLIC_STOP_INDEX_CAP: return "index-cap";
    case SNAPSHOT_SYMBOLIC_STOP_LABEL_CAP: return "label-cap";
    case SNAPSHOT_SYMBOLIC_STOP_MALFORMED: return "malformed";
    default: return "none";
    }
}

uint32_t snapshot_symbolic_run(const SnapshotSymbolicView *view,
                               SnapshotMutationProposalSink *sink)
{
    SnapshotSymbolicEngine engine;
    SnapshotSymbolicStageMark mark;
    SnapshotSymbolicStageMark submit_mark = { 0, 0 };
    bool submit_started = false;
    uint32_t generated = 0;
    uint32_t submitted = 0;

    snapshot_symbolic_configure();
    if (s_symbolic_config.mode == SNAPSHOT_SYMBOLIC_OFF) return 0;
    if (view == NULL || view->baseline == NULL || view->expr_base == NULL ||
        view->query_base == NULL || view->expr_entry < 0 ||
        view->expr_exit < view->expr_entry || view->query_entry < 0 ||
        view->query_exit < view->query_entry ||
        view->run_epoch != view->baseline->run_epoch) {
        return 0;
    }
    if (s_symbolic_config.mode == SNAPSHOT_SYMBOLIC_BOUNDARY && sink == NULL) {
        return 0;
    }

    memset(&engine, 0, sizeof(engine));
    engine.view = view;
    engine.budget.max_work = s_symbolic_config.max_work;
    engine.budget.max_bytes = s_symbolic_config.max_bytes;
    engine.budget.deadline_us = deadline_guard_us(s_symbolic_config.deadline_ms);
    engine.stats.start_us = g_get_monotonic_time();
    mark = stage_begin(&engine);
    {
        uint64_t source_bytes =
            (uint64_t)SNAPSHOT_SYMBOLIC_MAX_SOURCES * sizeof(*engine.sources);
        uint64_t lookup_bytes =
            (uint64_t)SNAPSHOT_SYMBOLIC_SOURCE_TABLE_CAPACITY *
            sizeof(*engine.source_lookup);
        uint64_t candidate_bytes =
            (uint64_t)SNAPSHOT_SYMBOLIC_MAX_SOURCES *
            SNAPSHOT_SYMBOLIC_MAX_CANDIDATES_PER_SOURCE *
            sizeof(*engine.candidates);
        uint64_t count_bytes =
            (uint64_t)SNAPSHOT_SYMBOLIC_MAX_SOURCES *
            sizeof(*engine.candidate_counts);

        if (!budget_reserve_bytes(&engine.budget, source_bytes + lookup_bytes +
                                                   candidate_bytes +
                                                   count_bytes)) {
            stage_end(&engine, SNAPSHOT_SYMBOLIC_STAGE_ALLOC, mark);
            stage_abort(&engine, SNAPSHOT_SYMBOLIC_STAGE_ALLOC);
            goto out;
        }
        engine.sources = symbolic_try_malloc0((size_t)source_bytes);
        engine.source_lookup = symbolic_try_malloc0((size_t)lookup_bytes);
        engine.candidates = symbolic_try_malloc0((size_t)candidate_bytes);
        engine.candidate_counts = symbolic_try_malloc0((size_t)count_bytes);
    }
    stage_end(&engine, SNAPSHOT_SYMBOLIC_STAGE_ALLOC, mark);
    if (engine.sources == NULL || engine.source_lookup == NULL ||
        engine.candidates == NULL || engine.candidate_counts == NULL) {
        /* Allocation failure before traversal: disable this advisor while
         * preserving every pre-existing family. */
        engine.stats.budget++;
        record_allocation_failure(&engine, SNAPSHOT_SYMBOLIC_STAGE_ALLOC);
        goto out;
    }
    mark = stage_begin(&engine);
    if (!index_init(&engine.index, &engine.budget)) {
        stage_end(&engine, SNAPSHOT_SYMBOLIC_STAGE_INDEX, mark);
        if (engine.budget.exhausted) {
            stage_abort(&engine, SNAPSHOT_SYMBOLIC_STAGE_INDEX);
        } else {
            engine.stats.budget++;
            record_allocation_failure(&engine, SNAPSHOT_SYMBOLIC_STAGE_INDEX);
        }
        goto out;
    }
    stage_end(&engine, SNAPSHOT_SYMBOLIC_STAGE_INDEX, mark);

    mark = stage_begin(&engine);
    if (!engine_select_sources(&engine)) {
        stage_end(&engine, SNAPSHOT_SYMBOLIC_STAGE_SOURCES, mark);
        stage_abort(&engine, SNAPSHOT_SYMBOLIC_STAGE_SOURCES);
        goto out;
    }
    stage_end(&engine, SNAPSHOT_SYMBOLIC_STAGE_SOURCES, mark);
    mark = stage_begin(&engine);
    if (!engine_bind_roots(&engine)) {
        stage_end(&engine, SNAPSHOT_SYMBOLIC_STAGE_ROOTS, mark);
        stage_abort(&engine, SNAPSHOT_SYMBOLIC_STAGE_ROOTS);
        goto out;
    }
    stage_end(&engine, SNAPSHOT_SYMBOLIC_STAGE_ROOTS, mark);
    mark = stage_begin(&engine);
    if (!engine_forward(&engine)) {
        stage_end(&engine, SNAPSHOT_SYMBOLIC_STAGE_FORWARD, mark);
        stage_abort(&engine, SNAPSHOT_SYMBOLIC_STAGE_FORWARD);
        goto out;
    }
    stage_end(&engine, SNAPSHOT_SYMBOLIC_STAGE_FORWARD, mark);
    mark = stage_begin(&engine);
    if (!engine_consumers(&engine)) {
        stage_end(&engine, SNAPSHOT_SYMBOLIC_STAGE_CONSUMERS, mark);
        stage_abort(&engine, SNAPSHOT_SYMBOLIC_STAGE_CONSUMERS);
        goto out;
    }
    stage_end(&engine, SNAPSHOT_SYMBOLIC_STAGE_CONSUMERS, mark);

    /* The complete analysis is the precondition for both the digest and the
     * would-submit summary: an interrupted scan has no comparable set. */
    engine.stats.analysis_complete = true;
    summarize_completed_analysis(&engine);

    if (s_symbolic_config.mode == SNAPSHOT_SYMBOLIC_BOUNDARY) {
        uint64_t proposal_bytes = 0;
        uint64_t submission_work = 0;

        submit_mark = stage_begin(&engine);
        submit_started = true;

        /* Reserve the complete bounded submission footprint and work before
         * publishing the first family.  Budget exhaustion therefore cannot
         * publish a prefix of this advisor's result. */
        for (uint32_t s = 0; s < engine.source_count; s++) {
            uint32_t count = engine.candidate_counts[s];
            if (!budget_step(&engine.budget, 1)) goto out;
            proposal_bytes += (uint64_t)count *
                (sizeof(SnapshotMutationProposalVariant) +
                 sizeof(SnapshotMutationProposalWrite));
            submission_work += (uint64_t)count * engine.sources[s].width;
        }
        if (!budget_reserve_bytes(&engine.budget, proposal_bytes) ||
            !budget_step(&engine.budget, submission_work)) {
            /* The whole submission allowance is refused before the first sink
             * call, so no family prefix is published. */
            goto out;
        }

        for (uint32_t s = 0; s < engine.source_count; s++) {
            const SnapshotSymbolicCandidate *selected[
                SNAPSHOT_SYMBOLIC_MAX_CANDIDATES_PER_SOURCE];
            uint32_t count = engine.candidate_counts[s];
            uint32_t emitted = 0;
            SnapshotSymbolicSubmitResult outcome;

            if (count == 0) continue;
            for (uint32_t ci = 0; ci < count; ci++) {
                selected[ci] = engine_candidate_at(&engine, s, ci);
            }
            outcome = submit_source(&engine, sink, selected, count, s,
                                    &emitted);
            if (emitted > 0) generated++;
            if (outcome == SNAPSHOT_SYMBOLIC_SUBMIT_REJECTED) {
                /* The sink rejected the family (quota or validation): a local
                 * abstention that leaves the source's generic alternatives
                 * intact. */
                engine.stats.unsupported++;
                engine.stats.submission_rejections++;
            } else if (outcome == SNAPSHOT_SYMBOLIC_SUBMIT_ALLOCATION) {
                record_allocation_failure(
                    &engine, SNAPSHOT_SYMBOLIC_STAGE_SUBMIT);
            } else if (emitted > 0) {
                submitted++;
            }
        }
    }

out:
    if (submit_started) {
        stage_end(&engine, SNAPSHOT_SYMBOLIC_STAGE_SUBMIT, submit_mark);
        stage_abort(&engine, SNAPSHOT_SYMBOLIC_STAGE_SUBMIT);
    }
    engine.stats.families_generated = generated;
    engine.stats.families = submitted;
    if (engine.budget.work_exhausted || engine.budget.bytes_exhausted ||
        engine.budget.deadline_exhausted) {
        engine.stats.budget++;
    }
    engine.stats.work = engine.budget.work;
    engine.stats.bytes = engine.budget.bytes;
    engine.stats.end_us = g_get_monotonic_time();
    log_msg("[symbolic-advisor] [summary] [mode %s] [sources %u] "
            "[valid-roots %u] [consumers %u] [candidates %u] [families %u] "
            "[unsupported %u] [budget %u] [work %llu] [bytes %llu] "
            "[time-ms %lld] [candidates-generated %u] "
            "[families-generated %u] [families-accepted %u]\n",
            s_symbolic_config.mode == SNAPSHOT_SYMBOLIC_BOUNDARY
                ? "boundary" : "shadow",
            engine.stats.sources, engine.stats.valid_roots,
            engine.stats.consumers, engine.stats.candidates,
            engine.stats.families, engine.stats.unsupported,
            engine.stats.budget, (unsigned long long)engine.stats.work,
            (unsigned long long)engine.stats.bytes,
            (long long)((engine.stats.end_us - engine.stats.start_us) / 1000),
            engine.stats.candidates_generated,
            engine.stats.families_generated, engine.stats.families);
    log_msg("[symbolic-advisor] [profile] [version 1] [mode %s] "
            "[max-work %llu] [max-bytes %llu] [deadline-ms %llu] "
            "[alloc-us %lld] [alloc-work %llu] "
            "[index-us %lld] [index-work %llu] "
            "[sources-us %lld] [sources-work %llu] "
            "[roots-us %lld] [roots-work %llu] "
            "[forward-us %lld] [forward-work %llu] "
            "[consumers-us %lld] [consumers-work %llu] "
            "[submit-us %lld] [submit-work %llu] "
            "[work-exhausted %u] [bytes-exhausted %u] "
            "[deadline-exhausted %u] [allocation-failures %u] "
            "[index-cap-refusals %u] [label-cap-refusals %u] "
            "[stop-stage %s] [stop-reason %s] "
            "[sources %u] [valid-roots %u] [candidates-validated %u] "
            "[would-submit-families %u] [would-submit-variants %u] "
            "[analysis-complete %u] [digest %016llx%016llx%016llx%016llx"
            "%016llx%016llx%016llx%016llx]\n",
            s_symbolic_config.mode == SNAPSHOT_SYMBOLIC_BOUNDARY
                ? "boundary" : "shadow",
            (unsigned long long)s_symbolic_config.max_work,
            (unsigned long long)s_symbolic_config.max_bytes,
            (unsigned long long)s_symbolic_config.deadline_ms,
            (long long)engine.stats.stage_us[SNAPSHOT_SYMBOLIC_STAGE_ALLOC],
            (unsigned long long)engine.stats.stage_work[
                SNAPSHOT_SYMBOLIC_STAGE_ALLOC],
            (long long)engine.stats.stage_us[SNAPSHOT_SYMBOLIC_STAGE_INDEX],
            (unsigned long long)engine.stats.stage_work[
                SNAPSHOT_SYMBOLIC_STAGE_INDEX],
            (long long)engine.stats.stage_us[SNAPSHOT_SYMBOLIC_STAGE_SOURCES],
            (unsigned long long)engine.stats.stage_work[
                SNAPSHOT_SYMBOLIC_STAGE_SOURCES],
            (long long)engine.stats.stage_us[SNAPSHOT_SYMBOLIC_STAGE_ROOTS],
            (unsigned long long)engine.stats.stage_work[
                SNAPSHOT_SYMBOLIC_STAGE_ROOTS],
            (long long)engine.stats.stage_us[SNAPSHOT_SYMBOLIC_STAGE_FORWARD],
            (unsigned long long)engine.stats.stage_work[
                SNAPSHOT_SYMBOLIC_STAGE_FORWARD],
            (long long)engine.stats.stage_us[
                SNAPSHOT_SYMBOLIC_STAGE_CONSUMERS],
            (unsigned long long)engine.stats.stage_work[
                SNAPSHOT_SYMBOLIC_STAGE_CONSUMERS],
            (long long)engine.stats.stage_us[SNAPSHOT_SYMBOLIC_STAGE_SUBMIT],
            (unsigned long long)engine.stats.stage_work[
                SNAPSHOT_SYMBOLIC_STAGE_SUBMIT],
            engine.budget.work_exhausted ? 1u : 0u,
            engine.budget.bytes_exhausted ? 1u : 0u,
            engine.budget.deadline_exhausted ? 1u : 0u,
            engine.stats.allocation_failures,
            engine.stats.index_cap_refusals,
            engine.stats.label_cap_refusals,
            engine.stats.stop_reason == SNAPSHOT_SYMBOLIC_STOP_NONE
                ? "none"
                : stage_name((SnapshotSymbolicStage)engine.stats.stop_stage),
            stop_reason_name((SnapshotSymbolicStop)engine.stats.stop_reason),
            engine.stats.sources, engine.stats.valid_roots,
            engine.stats.candidates_generated,
            engine.stats.would_submit_families,
            engine.stats.would_submit_variants,
            engine.stats.digest_complete ? 1u : 0u,
            (unsigned long long)engine.stats.digest[0],
            (unsigned long long)engine.stats.digest[1],
            (unsigned long long)engine.stats.digest[2],
            (unsigned long long)engine.stats.digest[3],
            (unsigned long long)engine.stats.digest[4],
            (unsigned long long)engine.stats.digest[5],
            (unsigned long long)engine.stats.digest[6],
            (unsigned long long)engine.stats.digest[7]);
    s_symbolic_last_stats = engine.stats;
    index_destroy(&engine.index);
    g_free(engine.candidate_counts);
    g_free(engine.candidates);
    g_free(engine.source_lookup);
    g_free(engine.sources);
    return submitted;
}
