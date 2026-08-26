#ifndef BINRADAR_OSPREY_INTERNAL_H
#define BINRADAR_OSPREY_INTERNAL_H

/*
 * Private OSPREY structures shared by the OSPREY translation units.
 * See osprey.h for the public API and the ownership model.
 *
 * The shared per-run transport (OspreySharedRun) lives in a MAP_SHARED
 * anonymous mapping created during snapshot_init(); it is mmap'd, never
 * malloc'd, so COW after fork keeps the parent's copy at the snapshot
 * baseline while the child's writes vanish at child exit.  All tables are
 * fixed-capacity open-addressed arrays; every index access is clamped and
 * overflow is sticky.
 */

#include "osprey.h"


/* ------------------------------------------------------------------ */
/* Canonical keys (full-field equality; hashes are bucket selectors)  */
/* ------------------------------------------------------------------ */

/* Full equality-comparable key.  A hash value is only a bucket selector;
 * object identity is the struct itself, compared field by field.  Never
 * pack or XOR-compose identities into a scalar. */
typedef struct OspreyKey {
    uint64_t tag;   /* discriminates key kinds */
    uint64_t w[10]; /* payload words (kind-specific layout) */
} OspreyKey;

static inline guint osprey_key_hash(gconstpointer p) {
    const OspreyKey *k = p;
    uint64_t h = k->tag;
    for (int i = 0; i < 10; i++) {
        h ^= k->w[i] + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    }
    return (guint)h;
}

static inline gboolean osprey_key_equal(gconstpointer p, gconstpointer q) {
    return memcmp(p, q, sizeof(OspreyKey)) == 0;
}

static inline OspreyKey osprey_region_key(const OspreyRegionId *r) {
    OspreyKey k;
    memset(&k, 0, sizeof(k));
    k.tag = 0x524547ULL; /* "REG" */
    k.w[0] = (uint64_t)r->kind;
    k.w[1] = r->code_image_id;
    k.w[2] = r->site_offset;
    return k;
}

static inline OspreyKey osprey_addr_key(const OspreyAddress *a) {
    OspreyKey k = osprey_region_key(&a->region);
    k.tag = 0x414444ULL; /* "ADD" */
    k.w[3] = (uint64_t)a->offset;
    return k;
}

static inline OspreyKey osprey_chunk_key(const OspreyChunk *c) {
    OspreyKey k = osprey_region_key(&c->address.region);
    k.tag = 0x43484BULL; /* "CHK" */
    k.w[3] = (uint64_t)c->address.offset;
    k.w[4] = c->size;
    return k;
}

/* (predicate kind, region) candidate-accounting key. */
static inline OspreyKey osprey_kind_region_key(uint8_t kind,
                                               const OspreyRegionId *r) {
    OspreyKey k = osprey_region_key(r);
    k.tag = 0x4B5247ULL; /* "KRG" */
    k.w[3] = kind;
    return k;
}

/* (instruction pc, region) pair key (CB02/CB08 grouping). */
static inline OspreyKey osprey_pc_region_key(uint64_t pc,
                                             const OspreyRegionId *r) {
    OspreyKey k = osprey_region_key(r);
    k.tag = 0x504352ULL; /* "PCR" */
    k.w[3] = pc;
    return k;
}

/* (region, offset) base key (decoder field grouping). */
static inline OspreyKey osprey_base_key(const OspreyRegionId *r, int64_t off) {
    OspreyKey k = osprey_region_key(r);
    k.tag = 0x425345ULL; /* "BSE" */
    k.w[3] = (uint64_t)off;
    return k;
}

/* Factor identity key: full-field equality (rule, head, polarity,
 * stage, probability, variable set).  A hash is only a bucket
 * selector; identity is the struct itself. */
typedef struct OspreyFactorKey {
    uint16_t rule;
    uint16_t head_idx;   /* index into var_ids (sorted) */
    uint8_t negative;
    uint8_t stage;
    uint64_t p_bits;     /* exact double bits of p */
    uint32_t num_vars;
    uint32_t var_ids[8];
} OspreyFactorKey;

guint osprey_factor_key_hash(gconstpointer p);
gboolean osprey_factor_key_equal(gconstpointer a, gconstpointer b);

/* ------------------------------------------------------------------ */
/* Fact records (child-written)                                        */
/* ------------------------------------------------------------------ */

typedef struct OspreyAccessFact {
    uint64_t pc;               /* normalized instruction offset */
    OspreyChunk chunk;
    uint32_t dynamic_count;
    uint32_t sample_support;   /* distinct unmodified samples */
    uint8_t is_store;
    uint8_t reserved[7];
} OspreyAccessFact;

typedef struct OspreyBaseFact {
    uint64_t pc;
    OspreyChunk chunk;         /* accessed chunk */
    OspreyAddress base;        /* tracked base address (region+offset) */
    uint64_t prov_object_id;   /* heap bases: provenance identity */
    uint32_t prov_generation;
    uint32_t sample_support;
    uint32_t reserved;
} OspreyBaseFact;

typedef struct OspreyCopyFact {
    OspreyChunk source;
    OspreyChunk destination;
    uint32_t sample_support;
    uint32_t reserved;
} OspreyCopyFact;

typedef struct OspreyPointsToFact {
    OspreyChunk pointer_chunk;
    OspreyAddress target;
    uint32_t sample_support;
    uint32_t weak_numeric_evidence;
} OspreyPointsToFact;

typedef struct OspreyMallocFact {
    uint64_t site_pc;          /* normalized allocator call site */
    int64_t requested_size;    /* -1 == failed; 0 == zero-size success */
    uint32_t sample_support;
    uint32_t reserved;
} OspreyMallocFact;

typedef struct OspreyMayArrayFact {
    OspreyAddress start;
    uint32_t element_count;
    uint32_t element_size;
    uint32_t evidence_kind;      /* 0 = allocation-argument heuristic */
    uint32_t sample_support;
} OspreyMayArrayFact;

/* One live canonical region instance (child-written): canonical region,
 * the raw runtime anchor it resolved to, and the observed raw span.
 * raw_base is the offset-zero anchor (entry SP for stack frames, heap
 * base, image base for the global region); raw_min/raw_max are the
 * lowest/highest observed raw addresses (stack: [min_sp, entry_sp];
 * heap: [base, base+size]; global: [image_base, image_base+span]).
 * Canonical offsets are signed relative to raw_base; the downward
 * stack is never treated as [entry_sp, entry_sp+extent).  The parent
 * uses these to map raw mutation addresses back to canonical chunks
 * (consumer cutover; Stage 7). */
typedef struct OspreyRegionInstance {
    OspreyRegionId region;
    uint64_t instance_id;      /* runtime identity within this process */
    uint64_t raw_base;
    uint64_t raw_min;          /* lowest observed raw address */
    uint64_t raw_max;          /* highest observed raw address */
    uint64_t prov_object_id;   /* heap: provenance identity */
    uint32_t prov_generation;
    uint32_t sample_support;
    uint32_t reserved;
} OspreyRegionInstance;

/* ------------------------------------------------------------------ */
/* Origin shadows (per-CPU, process-local; never shared)               */
/* ------------------------------------------------------------------ */

typedef enum OspreyOriginKind {
    OSPREY_ORIGIN_NONE = 0,
    OSPREY_ORIGIN_ADDRESS,   /* register holds a canonical address */
    OSPREY_ORIGIN_VALUE,     /* register holds a value loaded from a chunk */
} OspreyOriginKind;

typedef struct OspreyRegOrigin {
    uint8_t kind;              /* OspreyOriginKind */
    uint8_t valid;
    uint8_t reserved[2];
    target_ulong concrete_value; /* value-consistency check */
    OspreyChunk chunk;           /* VALUE: source chunk */
    OspreyAddress address;       /* ADDRESS: base address */
    uint64_t prov_object_id;     /* heap ADDRESS origins: provenance
                                  * identity (object_id, generation) */
    uint32_t prov_generation;
    uint32_t reserved2;
    uint64_t producer_pc;
} OspreyRegOrigin;

typedef struct OspreyMemSlotOrigin {
    uint8_t valid;
    uint8_t kind;              /* OspreyOriginKind */
    uint8_t reserved[6];
    OspreyChunk chunk;
    OspreyAddress address;
    target_ulong concrete_value;
    uint64_t prov_object_id;
    uint32_t prov_generation;
    uint32_t reserved2;
} OspreyMemSlotOrigin;

#define OSPREY_SHADOW_ALIGN 8

typedef struct OspreyCpuOriginState {
    OspreyRegOrigin regs[CPU_NB_REGS];
    /* Aligned native-width memory-shadow hash table.  Key = guest
     * address (aligned slot); value = OspreyMemSlotOrigin*. */
    GHashTable *mem_slots;
    /* Pending effective-address metadata (set before the guest access,
     * consumed after it succeeds). */
    uint8_t ea_valid;
    int32_t ea_base_reg;
    int32_t ea_index_reg;
    int32_t ea_scale;
    int64_t ea_disp;
    target_ulong ea_base_val;
    target_ulong ea_index_val;
    /* Address-mode state of the current instruction (aflags | (override
     * + 1) << 8) recorded by helper_sem_set_ea / helper_sem_mem_access.
     * The F01 eligibility gate (aflag == MO_64 && override < 0) is
     * consumer-side policy in helper_sem_mem_access; push/pop emit no
     * set_ea, so the mem-access event carries the mode itself. */
    uint32_t ea_mode;
    /* Origin snapshots taken at set_ea time: the base/index register may
     * be overwritten between set_ea and mem_access (e.g. mov (%rax),%rax
     * kills RAX); the F02 BaseAddr decision must use the pre-access
     * origin, never the post-access one. */
    OspreyRegOrigin ea_base_origin;
    OspreyRegOrigin ea_index_origin;
} OspreyCpuOriginState;

/* ------------------------------------------------------------------ */
/* Shared run (fixed layout, no pointers)                              */
/* ------------------------------------------------------------------ */

#define OSPREY_SHARED_VERSION 7u

struct OspreySharedRun {
    uint32_t version;
    uint32_t sample_id;
    /* Child-suffix observations (Stage 2.1: the baseline sample is the
     * union of the frozen pre-snapshot prefix and the per-child suffix;
     * see osprey_shared_run_freeze_prefix / osprey_shared_run_prepare). */
    uint64_t total_dynamic_observations;
    uint64_t total_samples;      /* committed unmodified samples */
    uint64_t total_dynamic_prefix;  /* frozen pre-snapshot dynamics */
    uint64_t total_facts_count;     /* unique facts in this sample */
    uint64_t prefix_facts_count;    /* frozen-prefix unique fact count */
    uint64_t max_facts_cfg;         /* config max_facts (child-side cap) */
    uint64_t max_chunks_cfg;        /* config max_chunks_per_region */
    uint32_t prefix_frozen;         /* freeze_prefix has run */

    /* Sticky overflow / error flags. */
    uint32_t overflow;           /* any table full / cap exhausted */
    uint32_t bad_region;         /* reserved; out-of-model addresses are
                                  * ordinary skips, never sticky */
    uint32_t bad_arithmetic;     /* checked arithmetic failed */
    uint32_t bad_identity;       /* provenance/object contract mismatch */
    uint32_t unsupported_execution; /* unsupported guest contract observed */
    uint32_t first_dropped_kind; /* fact kind of first dropped record */
    uint64_t first_dropped_hash; /* hash of the first dropped record */

    /* Open-addressed fact tables. Capacities are derived from config at
     * reset time; a capacity of 0 disables the table.  Each capacity
     * applies to both the prefix and the suffix family. */
    uint32_t access_cap;
    uint32_t access_used;
    uint32_t base_cap;
    uint32_t base_used;
    uint32_t copy_cap;
    uint32_t copy_used;
    uint32_t points_cap;
    uint32_t points_used;
    uint32_t alloc_cap;
    uint32_t alloc_used;
    uint32_t mayarray_cap;
    uint32_t mayarray_used;
    uint32_t region_cap;
    uint32_t region_used;
    uint32_t census_chunk_cap;
    uint32_t census_chunk_used;
    uint32_t census_region_cap;
    uint32_t census_region_used;
    /* Frozen prefix record counts (osprey_shared_run_freeze_prefix). */
    uint32_t prefix_access_used;
    uint32_t prefix_base_used;
    uint32_t prefix_copy_used;
    uint32_t prefix_points_used;
    uint32_t prefix_alloc_used;
    uint32_t prefix_mayarray_used;
    uint32_t prefix_region_used;
    /* Sticky state captured at freeze.  prepare restores these values
     * before every child suffix so a pre-snapshot failure cannot be
     * cleared by the forkserver reset. */
    uint32_t prefix_overflow;
    uint32_t prefix_bad_region;
    uint32_t prefix_bad_arithmetic;
    uint32_t prefix_bad_identity;
    uint32_t prefix_unsupported_execution;
    uint32_t prefix_first_dropped_kind;
    uint64_t prefix_first_dropped_hash;

    uint8_t storage[]; /* flex array; offsets computed in osprey.c */
};

/* Bucket kinds for the storage layout (osprey_shared_run_size). */
#define OSPREY_TABLE_ACCESS 0
#define OSPREY_TABLE_BASE   1
#define OSPREY_TABLE_COPY   2
#define OSPREY_TABLE_POINTS 3
#define OSPREY_TABLE_ALLOC  4
#define OSPREY_TABLE_MAYARR 5
#define OSPREY_TABLE_REGION 6
#define OSPREY_TABLE_CENSUS_CHUNK 7
#define OSPREY_TABLE_CENSUS_REGION 8
#define OSPREY_TABLE_COUNT  9

/* Primary fact tables (per-child suffix family); the prefix and census
 * families extend the layout (osprey.c). */
#define OSPREY_TABLE_PRIMARY_COUNT 7

/* Stage 2.1 census tables: enforced per-sample unique-chunk and
 * per-region chunk limits.  These are counting tables only (no sample
 * support), keyed by the same full-field identity used for facts.
 * Exhausting a census limit sets run->overflow (cap exhaustion),
 * which rejects the merge fail-closed. */
typedef struct OspreyCensusChunk {
    OspreyChunk chunk;
} OspreyCensusChunk;

typedef struct OspreyCensusRegion {
    OspreyRegionId region;
    uint32_t chunk_count;   /* unique chunks observed in this region */
    uint32_t reserved;
} OspreyCensusRegion;

uint64_t osprey_census_chunk_hash(const OspreyCensusChunk *f);
bool osprey_census_chunk_eq(const OspreyCensusChunk *a,
                            const OspreyCensusChunk *b);
uint64_t osprey_census_region_hash(const OspreyCensusRegion *f);
bool osprey_census_region_eq(const OspreyCensusRegion *a,
                             const OspreyCensusRegion *b);

/* Hash/equality over the fixed records (osprey-facts.c). */
uint64_t osprey_access_hash(const OspreyAccessFact *f);
bool osprey_access_eq(const OspreyAccessFact *a, const OspreyAccessFact *b);
uint64_t osprey_base_hash(const OspreyBaseFact *f);
bool osprey_base_eq(const OspreyBaseFact *a, const OspreyBaseFact *b);
/* Provenance-authoritative heap origin check (osprey-facts.c). */
bool osprey_origin_prov_live(const OspreyRegOrigin *o);
uint64_t osprey_copy_hash(const OspreyCopyFact *f);
bool osprey_copy_eq(const OspreyCopyFact *a, const OspreyCopyFact *b);
uint64_t osprey_points_hash(const OspreyPointsToFact *f);
bool osprey_points_eq(const OspreyPointsToFact *a, const OspreyPointsToFact *b);
uint64_t osprey_alloc_hash(const OspreyMallocFact *f);
bool osprey_alloc_eq(const OspreyMallocFact *a, const OspreyMallocFact *b);
uint64_t osprey_mayarray_hash(const OspreyMayArrayFact *f);
 bool osprey_mayarray_eq(const OspreyMayArrayFact *a,
                         const OspreyMayArrayFact *b);
uint64_t osprey_region_instance_hash(const OspreyRegionInstance *f);
bool osprey_region_instance_eq(const OspreyRegionInstance *a,
                               const OspreyRegionInstance *b);

/* Shared-run storage accessor (osprey.c). */
uint8_t *osprey_run_table(OspreySharedRun *run, int table);

/* Validate that a shared-run header describes exactly the layout derived
 * from the active configuration before any table offset is trusted. */
bool osprey_shared_run_layout_valid(const OspreyConfig *config,
                                    const OspreySharedRun *run);

/* Image normalization base (osprey.c). */
target_ulong osprey_get_image_base(void);
target_ulong osprey_get_image_end(void);

/* Key allocation helpers (osprey.c). */
OspreyKey *osprey_key_new(const OspreyKey *k);
void osprey_key_free(gpointer p);

/* Main-image writable global range (merged interval set). */
typedef struct OspreyGlobalRange {
    int64_t offset;   /* image-relative */
    uint64_t extent;
} OspreyGlobalRange;

/* Merge a writable main-image range into the interval set (osprey.c). */
void global_ranges_add(OspreyContext *ctx, target_ulong base,
                       uint64_t size);

/* Resolve a runtime address into the main-image global region. */
bool osprey_global_of_addr(target_ulong addr, OspreyRegionId *region,
                           int64_t *offset);

/* Module-level context pointer (child-side helpers). */
OspreyContext *osprey_ctx_ref(void);
void osprey_ctx_ref_set(OspreyContext *ctx);

/* Open-addressing table helpers (osprey-facts.c).  Returns 1 on insert
 * or 0 on duplicate update; sets *dropped when the table is full. */
int osprey_table_insert_access(OspreySharedRun *run, const OspreyAccessFact *f);
int osprey_table_insert_base(OspreySharedRun *run, const OspreyBaseFact *f);
int osprey_table_insert_copy(OspreySharedRun *run, const OspreyCopyFact *f);
int osprey_table_insert_points(OspreySharedRun *run, const OspreyPointsToFact *f);
int osprey_table_insert_alloc(OspreySharedRun *run, const OspreyMallocFact *f);
int osprey_table_insert_mayarray(OspreySharedRun *run, const OspreyMayArrayFact *f);
int osprey_table_insert_region(OspreySharedRun *run,
                               const OspreyRegionInstance *f);
/* Stage 2.1 census inserts: count unique chunks/regions per sample.
 * Returns 1 on new record, 0 on duplicate, -1 on limit exhausted
 * (sets run->overflow). */
int osprey_table_insert_census_chunk(OspreySharedRun *run,
                                     const OspreyCensusChunk *f);
int osprey_table_insert_census_region(OspreySharedRun *run,
                                      const OspreyCensusRegion *f);

/* Iteration (parent side).  table == OSPREY_TABLE_* primary tables;
 * the prefix family of a primary table is iterated with
 * OSPREY_TABLE_PREFIX(OSPREY_TABLE_*). */
typedef struct OspreyRunIter {
    const OspreySharedRun *run;
    int table;      /* OSPREY_TABLE_* or prefix family */
    uint32_t slot;
    uint32_t used;
} OspreyRunIter;
int osprey_run_iter_next(OspreyRunIter *it, const void **record);

/* Prefix-family tables: the frozen pre-snapshot records for a primary
 * table live in a second region of the shared run with the same record
 * size and capacity (see osprey.c layout).  The parent iterates them
 * through the same record format so `prefix ∪ child` merges as one
 * deduplicated sample. */
#define OSPREY_TABLE_PREFIX_ACCESS    (OSPREY_TABLE_COUNT + 0)
#define OSPREY_TABLE_PREFIX_BASE      (OSPREY_TABLE_COUNT + 1)
#define OSPREY_TABLE_PREFIX_COPY      (OSPREY_TABLE_COUNT + 2)
#define OSPREY_TABLE_PREFIX_POINTS    (OSPREY_TABLE_COUNT + 3)
#define OSPREY_TABLE_PREFIX_ALLOC     (OSPREY_TABLE_COUNT + 4)
#define OSPREY_TABLE_PREFIX_MAYARR    (OSPREY_TABLE_COUNT + 5)
#define OSPREY_TABLE_PREFIX_REGION    (OSPREY_TABLE_COUNT + 6)
#define OSPREY_PREFIX_TABLE_COUNT     7

/* Prefix record counts (occupied open slots).  The prefix is frozen by
 * copying primary-table records into the prefix region at
 * osprey_shared_run_freeze_prefix; osprey_run_prefix_used() returns the
 * occupied count. */
uint32_t osprey_run_prefix_used(const OspreySharedRun *run, int table);

/* Stage 2.1: reset the per-sample census tables and rebuild them from
 * the frozen prefix family, so a prepared sample's census is exactly
 * `prefix ∪ (empty suffix)` and later forks (mutation iterations) start
 * from a clean per-sample census. */
void osprey_census_rebuild_from_prefix(OspreySharedRun *run);

/* ------------------------------------------------------------------ */
/* Context (parent-owned)                                              */
/* ------------------------------------------------------------------ */

typedef struct OspreyGraph OspreyGraph; /* Stage 3 factor graph */

struct OspreyContext {
    OspreyConfig config;
    OspreySharedRun *shared;   /* attached in child; NULL in parent */
    QemuMutex shared_lock;     /* child-side insert mutex */

    /* Pre-sample fatal state: set by registration-time failures that
     * precede the sample transaction (e.g. ELF/global range overflow).
     * Copied into every reset shared run so the baseline merge rejects
     * (fail-closed); silent range omission is never acceptance. */
    bool pre_sample_fatal;
    const char *pre_sample_reason;

    /* Main-image writable global ranges (merged interval set). */
    GArray *global_ranges;     /* OspreyGlobalRange, sorted by offset */

    /* Analysis transaction state (parent side).  tx_status is sticky
     * for the current baseline transaction: once non-OK it never
     * returns to OK until the next complete baseline analysis, and no
     * model is installed or exposed.  tx_stage names the first failing
     * stage ("merge", "closure", "secondary", "infer", "decode"). */
    OspreyStatus tx_status;
    const char *tx_stage;
    const char *tx_reason;
    bool tx_model_ready;

    /* Staged graph/model built off to the side by the current
     * transaction; installed into ctx->graph/ctx->model only on
     * OSPREY_OK.  Freed on rejection. */
    OspreyGraph *staged_graph;
    OspreyModel *staged_model;

    /* Committed parent-side aggregate tables (grown in memory). */
    GArray *access_facts;      /* OspreyAccessFact (dedup, merged) */
    GArray *base_facts;        /* OspreyBaseFact */
    GArray *copy_facts;        /* OspreyCopyFact */
    GArray *points_facts;      /* OspreyPointsToFact */
    GArray *alloc_facts;       /* OspreyMallocFact */
    GArray *mayarray_facts;    /* OspreyMayArrayFact */
    GArray *region_instances;  /* OspreyRegionInstance (raw->canonical) */

    uint64_t total_samples;    /* committed unmodified samples */
    uint64_t total_dynamic_observations;

    /* Region catalog (parent side): runtime instances resolved at
     * collection time. */
    GArray *runtime_regions;   /* OspreyRuntimeRegion */

    /* Origin shadows, keyed by CPUArchState* (per-thread). */
    GHashTable *cpu_origins;   /* env* -> OspreyCpuOriginState* */

    /* Image normalization base (== symbolic_start_code). */
    target_ulong image_base;
    bool image_base_set;

    /* Committed model (installed only by a successful transaction). */
    OspreyModel *model;
    OspreyStatus last_status;
    uint64_t last_analyze_time_ms;

    /* Committed Stage 3 factor graph (parent side). */
    OspreyGraph *graph;
};

typedef struct OspreyRuntimeRegion {
    OspreyRegionId canonical;
    uint64_t instance_id;
    target_ulong base;
    uint64_t extent;      /* observed low/high bound or requested size */
    bool live;
} OspreyRuntimeRegion;

/* Runtime helpers used across OSPREY files. */
OspreyCpuOriginState *osprey_cpu_origin(CPUArchState *env);
bool osprey_region_of_addr(CPUArchState *env, target_ulong addr,
                           OspreyRegionId *region, int64_t *offset,
                           bool create);
void osprey_free_runtime_regions(void);
void osprey_log_sticky(const OspreySharedRun *run, const char *tag);

/* Mark the context with a pre-sample fatal condition (registration-time
 * arithmetic failure).  Every subsequently reset shared run carries the
 * bad_arithmetic flag so the baseline merge rejects. */
void osprey_mark_pre_sample_fatal(OspreyContext *ctx, const char *reason);

/* Clear the module-global pre-sample fatal state (unit-test isolation;
 * the real tracer never clears it after registration). */
void osprey_clear_pre_sample_fatal(void);

/* Fail-closed transaction helpers (osprey-facts.c). */
void osprey_tx_begin(OspreyContext *ctx);
void osprey_tx_reject(OspreyContext *ctx, OspreyStatus st,
                      const char *stage, const char *reason);
bool osprey_tx_ok(const OspreyContext *ctx);
OspreyStatus osprey_tx_status(const OspreyContext *ctx);
const char *osprey_tx_stage(const OspreyContext *ctx);
void osprey_tx_install(OspreyContext *ctx);
void osprey_tx_abort(OspreyContext *ctx);

/* Checked arithmetic (returns false on overflow and sets bad_arithmetic). */
bool osprey_check_add(int64_t a, int64_t b, int64_t *out);
bool osprey_check_mul(uint64_t a, uint64_t b, uint64_t *out);
bool osprey_check_sub(int64_t a, int64_t b, int64_t *out);

/* Decoded object kinds (osprey.h references OspreyDecodedKind). */
typedef enum OspreyDecodedKind {
    OSPREY_DECODED_UNKNOWN = 0,
    OSPREY_DECODED_PRIMITIVE,   /* width-preserving placeholder */
    OSPREY_DECODED_SCALAR,      /* Scalar(v) */
    OSPREY_DECODED_ARRAY,       /* Array(a1,a2,s) */
    OSPREY_DECODED_STRUCT,      /* field group under a base */
    OSPREY_DECODED_POINTER,     /* Pointer(v,a) */
    OSPREY_DECODED_FIELD,       /* FieldOf(v,a): field chunk */
    OSPREY_DECODED_ARRAY_START, /* ArrayStart(a) */
} OspreyDecodedKind;

/* ------------------------------------------------------------------ */
/* Stage 3+: predicate interning and factor graph                      */
/* ------------------------------------------------------------------ */

/* Predicate kinds (P01-P11 of the reference).  Each concrete predicate
 * instance is one Boolean random variable. */
typedef enum OspreyPredicateKind {
    OSPREY_PRED_NONE = 0,
    OSPREY_PRED_PRIMITIVE_VAR,     /* P01 PrimitiveVar(v) */
    OSPREY_PRED_PRIMITIVE_ACCESS,  /* P02 PrimitiveAccess(i,v) */
    OSPREY_PRED_UNFOLDABLE_HEAP,   /* P03 UnfoldableHeap(i,s) */
    OSPREY_PRED_FOLDABLE_HEAP,     /* P04 FoldableHeap(i,s) */
    OSPREY_PRED_HOMO_SEGMENT,      /* P05 HomoSegment(a1,a2,s) */
    OSPREY_PRED_ARRAY_START,       /* P06 ArrayStart(a) */
    OSPREY_PRED_SCALAR,            /* P07 Scalar(v) */
    OSPREY_PRED_ARRAY,             /* P08 Array(a1,a2,s) */
    OSPREY_PRED_FIELD_OF,          /* P09 FieldOf(v,a) */
    OSPREY_PRED_POINTER,           /* P10 Pointer(v,a) */
    OSPREY_PRED_COUNT
} OspreyPredicateKind;

/* Variable payload (kind determines which member is meaningful). */
typedef union OspreyVarPayload {
    OspreyChunk chunk;             /* primitive / scalar */
    struct {
        OspreyChunk chunk;
        uint64_t insn_pc;          /* normalized instruction offset */
    } prim_access;
    struct {
        OspreyRegionId region;     /* H_i */
        uint64_t size;
    } heap_fold;                   /* unfoldable / foldable */
    struct {
        OspreyAddress a1;          /* region-anchor address */
        OspreyAddress a2;          /* partner address */
        int64_t size;              /* segment length / stride */
    } segment;                     /* homo segment / array interval */
    OspreyAddress addr;            /* array start */
    struct {
        OspreyChunk chunk;         /* the accessed chunk */
        OspreyAddress base;        /* field base / pointer target */
    } attached;                    /* field-of / pointer */
} OspreyVarPayload;

typedef struct OspreyVar {
    uint32_t id;                   /* stable ordinal into ctx->graph->vars */
    uint8_t kind;                  /* OspreyPredicateKind */
    uint8_t hard_false;            /* CB06-style hard constraint */
    uint8_t region_limit_hit;      /* per-region candidate cap exceeded */
    uint8_t reserved;
    double belief;                 /* current marginal (Stages 4/5 fill) */
    OspreyVarPayload payload;
} OspreyVar;

/* Rule codes for factor provenance. */
typedef enum OspreyRuleCode {
    OSPREY_RULE_NONE = 0,
    OSPREY_RULE_CA01, OSPREY_RULE_CA02, OSPREY_RULE_CA03, OSPREY_RULE_CA04,
    OSPREY_RULE_CA05, OSPREY_RULE_CA06, OSPREY_RULE_CA07, OSPREY_RULE_CA08,
    OSPREY_RULE_CB01, OSPREY_RULE_CB02, OSPREY_RULE_CB03, OSPREY_RULE_CB04,
    OSPREY_RULE_CB05, OSPREY_RULE_CB06, OSPREY_RULE_CB07, OSPREY_RULE_CB08,
    OSPREY_RULE_CB09, OSPREY_RULE_CC01, OSPREY_RULE_CC02, OSPREY_RULE_CC03,
    OSPREY_RULE_CC04, OSPREY_RULE_CC05, OSPREY_RULE_CC06, OSPREY_RULE_CC07,
    OSPREY_RULE_CD01, OSPREY_RULE_CD02, OSPREY_RULE_CD03, OSPREY_RULE_CD04,
    OSPREY_RULE_CD05, OSPREY_RULE_CD06, OSPREY_RULE_CD07, OSPREY_RULE_CD08,
    OSPREY_RULE_CD09, OSPREY_RULE_CD10, OSPREY_RULE_CD11,
} OspreyRuleCode;

/* One instantiated rule instance: a factor over its variables.  The
 * generic convention (§7.1): weight p everywhere except the penalized
 * assignment "all antecedents true AND head violates the implication
 * direction" which gets weight 1-p.  head_idx indexes var_ids; for
 * multi-head rules each head gets its own factor (split). */
typedef struct OspreyFactor {
    uint32_t id;
    uint16_t rule;                 /* OspreyRuleCode */
    uint16_t head_idx;             /* index into var_ids; UINT16_MAX=unary */
    uint8_t negative;              /* 1 = negative implication */
    uint8_t stage;                 /* 1 = base (static), 2 = secondary */
    double p;                      /* support weight */
    uint32_t num_vars;
    uint32_t *var_ids;
} OspreyFactor;

/* Candidate/limit accounting per (kind, region). */
typedef struct OspreyKindRegionCount {
    uint64_t kept;
    uint64_t dropped;
} OspreyKindRegionCount;

/* R10-R12 hint instances: parallel-copy / unified-access / points-to
 * evidence for homomorphic segments.  a1 and a2 are region-anchor
 * addresses; size is the common offset delta s. */
typedef struct OspreyHint {
    OspreyAddress a1;
    OspreyAddress a2;
    int64_t size;
    uint8_t kind;                  /* 0=DataFlow, 1=UnifiedAccess, 2=PointsTo */
    uint8_t reserved[7];
    uint64_t instances;            /* supporting fact-instances */
} OspreyHint;

struct OspreyGraph {
    GArray *vars;                  /* OspreyVar */
    GHashTable *var_index;         /* OspreyKey* → (var_id+1) */
    GArray *hints;                 /* OspreyHint (deduped) */
    GArray *factors;               /* OspreyFactor* */
    GHashTable *factor_index;      /* OspreyKey* → (factor_id+1) */
    /* per (kind, region-key) candidate accounting */
    GHashTable *kind_region;       /* OspreyKey* → OspreyKindRegionCount* */
    /* union-find over vars (component partition for inference) */
    uint32_t *uf_parent;
    uint32_t uf_size;
    uint64_t hint_instances;       /* total R10-R12 hint instances */
    uint64_t limit_rows;           /* [osprey] [limit] rows emitted */
    uint64_t cd04_extensions;      /* CD04 closure extensions */
};

/* Stage 3 entry (legacy function name): deterministic closure (R01-R12),
 * predicate interning, bounded candidate generation, and static factor
 * instantiation.  Does not solve anything. */
OspreyStatus osprey_stage2_closure(OspreyContext *ctx);

/* Ownership: free a factor graph or decoded model (osprey-rules.c /
 * osprey-decode.c). */
OspreyGraph *osprey_graph_new(void);
void osprey_graph_free(OspreyGraph *g);
void osprey_model_free(OspreyModel *m);

/* Stage 3 secondary construction (legacy function name): deterministic
 * rules (CB02-CB09, CC04/CC05, CD07, CD08) whose preconditions are fact-
 * or candidate-driven.  Belief-dependent folding (CC07) is deferred to
 * the Stage 5 dynamic closure. */
OspreyStatus osprey_stage2_secondary(OspreyContext *ctx);

/* Stages 4/5 inference (osprey-infer.c): exact base inference followed
 * by secondary loopy BP.  The current implementation is non-conformant. */
OspreyStatus osprey_infer(OspreyContext *ctx);

/* Shared graph builders (osprey-rules.c); used by Stage 3 construction
 * and the Stage 5 dynamic closure. */
uint32_t osprey_intern_var(OspreyContext *ctx, uint8_t kind,
                           const OspreyVarPayload *payload);
void osprey_factor_add(OspreyContext *ctx, uint16_t rule, uint16_t head_idx,
                        bool negative, double p, const uint32_t *var_ids,
                        uint32_t num_vars);

/* One raw-address span mapping back to a decoded object (built at
 * decode time from the merged region instances). */
typedef struct OspRawSpan {
    uint64_t raw_start;
    uint64_t raw_end;      /* exclusive; == raw_start for point bases */
    uint32_t obj_idx;      /* into model->objects */
    uint8_t is_chunk;      /* 1 = exact chunk start+size semantics */
    uint8_t reserved[3];
} OspRawSpan;

/* Decoded model (installed by osprey_decode; parent side). */
struct OspreyModel {
    GArray *objects;       /* OspreyDecodedObject, insertion order */
    GHashTable *by_chunk;  /* OspreyKey* -> (index+1) */
    GArray *type_names;    /* char* type names (type_id = idx) */
    GArray *raw_spans;     /* OspRawSpan, sorted by raw_start */
    GHashTable *fields_by_base; /* OspreyKey* -> GArray(uint32 obj idx) */
    GHashTable *ptr_by_chunk; /* OspreyKey* -> pointer obj (index+1);
                                 independent of scalar/field exclusivity */
};

/* Stage 6 entry (osprey-decode.c): consistent decoding of posterior
 * predicates (§10 of the reference): hard-false/threshold discard,
 * per-chunk exclusivity between scalar/field/pointer/array-element,
 * non-overlapping field layouts per base, weighted interval array
 * selection, one pointer target base, deterministic naming, posterior
 * on every declaration. */
OspreyStatus osprey_decode(OspreyContext *ctx);

#endif /* BINRADAR_OSPREY_INTERNAL_H */
