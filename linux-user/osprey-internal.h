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
/* Canonical keys (used as open-addressing hashes, deterministic)      */
/* ------------------------------------------------------------------ */

typedef uint64_t OspreyKey; /* 64-bit canonical hash of the identity */

/* Canonical hash of a region id: kind (2b) | image (8b) | site (54b). */
static inline OspreyKey osprey_region_key(const OspreyRegionId *r) {
    uint64_t k = (uint64_t)(uint32_t)r->kind;
    k |= ((uint64_t)(r->code_image_id & 0xff)) << 8;
    k |= ((uint64_t)(r->site_offset & (((uint64_t)1 << 54) - 1))) << 16;
    return k;
}

static inline OspreyKey osprey_chunk_key(const OspreyChunk *c) {
    /* region key | signed-offset (48b) | size (12b) */
    uint64_t k = osprey_region_key(&c->address.region);
    uint64_t off = (uint64_t)(c->address.offset & (((uint64_t)1 << 48) - 1));
    k ^= off << 1;
    k ^= (c->size & 0xfff) << 49;
    return k;
}

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
 * the raw runtime base it resolved to, and the observed extent.  The
 * parent uses these to map raw mutation addresses back to canonical
 * chunks (consumer cutover; Stage 4). */
typedef struct OspreyRegionInstance {
    OspreyRegionId region;
    uint64_t raw_base;
    uint64_t extent;
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
    uint64_t producer_pc;
} OspreyRegOrigin;

typedef struct OspreyMemSlotOrigin {
    uint8_t valid;
    uint8_t kind;              /* OspreyOriginKind */
    uint8_t reserved[6];
    OspreyChunk chunk;
    OspreyAddress address;
    target_ulong concrete_value;
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

#define OSPREY_SHARED_VERSION 2u

struct OspreySharedRun {
    uint32_t version;
    uint32_t sample_id;
    uint64_t total_dynamic_observations;
    uint64_t total_samples;      /* committed unmodified samples */

    /* Sticky overflow / error flags. */
    uint32_t overflow;           /* any table full */
    uint32_t bad_region;         /* access failed region resolution */
    uint32_t bad_arithmetic;     /* checked arithmetic failed */
    uint32_t unsupported_execution; /* unsupported guest contract observed */
    uint32_t first_dropped_kind; /* fact kind of first dropped record */
    OspreyKey first_dropped_key;

    /* Open-addressed fact tables. Capacities are derived from config at
     * reset time; a capacity of 0 disables the table. */
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
#define OSPREY_TABLE_COUNT  7

/* Hash/equality over the fixed records (osprey-facts.c). */
uint64_t osprey_access_hash(const OspreyAccessFact *f);
bool osprey_access_eq(const OspreyAccessFact *a, const OspreyAccessFact *b);
uint64_t osprey_base_hash(const OspreyBaseFact *f);
bool osprey_base_eq(const OspreyBaseFact *a, const OspreyBaseFact *b);
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

/* Iteration (parent side). */
typedef struct OspreyRunIter {
    const OspreySharedRun *run;
    int table;      /* OSPREY_TABLE_* */
    uint32_t slot;
    uint32_t used;
} OspreyRunIter;
int osprey_run_iter_next(OspreyRunIter *it, const void **record);

/* ------------------------------------------------------------------ */
/* Context (parent-owned)                                              */
/* ------------------------------------------------------------------ */

typedef struct OspreyGraph OspreyGraph; /* Stage-2 factor graph */

struct OspreyContext {
    OspreyConfig config;
    OspreySharedRun *shared;   /* attached in child; NULL in parent */
    QemuMutex shared_lock;     /* child-side insert mutex */

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

    /* Committed Stage-2 factor graph (parent side). */
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
void osprey_log_sticky(const OspreySharedRun *run, const char *tag);

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
/* Stage 2+: predicate interning and factor graph                      */
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
    double belief;                 /* current marginal (Stage 3 fills) */
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
    GHashTable *var_index;         /* OspreyKey → (var_id+1) */
    GArray *hints;                 /* OspreyHint (deduped) */
    GArray *factors;               /* OspreyFactor* */
    GHashTable *factor_index;      /* OspreyKey → (factor_id+1) */
    /* per (kind, region-key) candidate accounting */
    GHashTable *kind_region;       /* key → OspreyKindRegionCount* */
    /* union-find over vars (component partition for inference) */
    uint32_t *uf_parent;
    uint32_t uf_size;
    uint64_t hint_instances;       /* total R10-R12 hint instances */
    uint64_t limit_rows;           /* [osprey] [limit] rows emitted */
    uint64_t cd04_extensions;      /* CD04 closure extensions */
};

/* Stage 2 entry: deterministic closure (R01-R12), predicate interning,
 * bounded candidate generation, and static factor instantiation.
 * Does not solve anything. */
OspreyStatus osprey_stage2_closure(OspreyContext *ctx);

/* Ownership: free a factor graph or decoded model (osprey-rules.c /
 * osprey-decode.c). */
OspreyGraph *osprey_graph_new(void);
void osprey_graph_free(OspreyGraph *g);
void osprey_model_free(OspreyModel *m);

/* Stage 3 entry: secondary deterministic rules (CB02-CB09, CC04/CC05,
 * CD07, CD08) whose preconditions are fact- or candidate-driven; adds
 * stage-2 factors to the graph.  Belief-dependent folding (CC07) is
 * deferred until after the first inference pass. */
OspreyStatus osprey_stage2_secondary(OspreyContext *ctx);

/* Stage 3 inference (osprey-infer.c): exact bucket elimination per
 * bounded component over stage-1 factors, then log-domain loopy BP over
 * the full graph seeded from the exact beliefs. */
OspreyStatus osprey_infer(OspreyContext *ctx);

/* Shared graph builders (osprey-rules.c); used by the folding closure
 * and the Stage-3 dynamic rules. */
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
    GHashTable *by_chunk;  /* osprey_chunk_key -> (index+1) */
    GArray *type_names;    /* char* type names (type_id = idx) */
    GArray *raw_spans;     /* OspRawSpan, sorted by raw_start */
    GHashTable *fields_by_base; /* base key -> GArray(uint32 obj idx) */
    GHashTable *ptr_by_chunk; /* osprey_chunk_key -> pointer obj (index+1);
                                 independent of scalar/field exclusivity */
};

/* Stage 4 entry (osprey-decode.c): consistent decoding of posterior
 * predicates (§10 of the reference): hard-false/threshold discard,
 * per-chunk exclusivity between scalar/field/pointer/array-element,
 * non-overlapping field layouts per base, weighted interval array
 * selection, one pointer target base, deterministic naming, posterior
 * on every declaration. */
OspreyStatus osprey_decode(OspreyContext *ctx);

#endif /* BINRADAR_OSPREY_INTERNAL_H */
