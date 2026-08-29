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
    const OspreyKey *a = p;
    const OspreyKey *b = q;
    if (a->tag != b->tag) return FALSE;
    for (size_t i = 0; i < G_N_ELEMENTS(a->w); i++) {
        if (a->w[i] != b->w[i]) return FALSE;
    }
    return TRUE;
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

#define OSPREY_FACTOR_MAX_ARITY 4u

/* Factor identity key: full-field equality over the semantic formula.
 * Variable order is meaningful: it is never sorted or reconstructed from
 * numeric variable IDs.  Unused words are zeroed before hashing. */
typedef struct OspreyFactorKey {
    uint16_t rule;
    uint8_t stage;
    uint8_t potential_kind;
    uint8_t negative;
    uint8_t reserved;
    uint16_t head_idx;       /* 0 for prior; UINT16_MAX for hard false */
    uint16_t reserved2;
    uint64_t p_bits;         /* exact double bits of target-true p */
    uint32_t num_vars;
    uint32_t var_ids[OSPREY_FACTOR_MAX_ARITY];
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
    uint8_t op_class;           /* SemOpClass, serialized for F01 audits */
    uint8_t reserved[6];
} OspreyAccessFact;

typedef struct OspreyBaseFact {
    uint64_t pc;
    OspreyChunk chunk;         /* accessed chunk */
    OspreyAddress base;        /* tracked base address (region+offset) */
    uint64_t prov_object_id;   /* heap bases: provenance identity */
    uint32_t prov_generation;
    uint64_t producer_pc;      /* normalized origin producer PC (audit
                                * metadata; not part of logical identity) */
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
    uint64_t requested_size;   /* successful-request bytes only
                                * (0 == zero-size success); failed
                                * calls are diagnostics, never facts */
    uint32_t sample_support;
    uint32_t reserved;
} OspreyMallocFact;

/* MayArray evidence kinds (Stage 2.5): only checked positive calloc
 * geometry is published. */
#define OSPREY_MAY_ARRAY_CALLOC_GEOMETRY 0u

typedef struct OspreyMayArrayFact {
    OspreyAddress start;
    uint64_t element_count;    /* positive calloc count */
    uint64_t element_size;     /* positive calloc element size */
    uint32_t evidence_kind;    /* OSPREY_MAY_ARRAY_* */
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
/* Stage 3.1 parent-local deterministic relations                      */
/* ------------------------------------------------------------------ */

/* F01's class and direction are intentionally absent from this derived
 * projection.  The parent creates one row per (pc, complete chunk) while
 * the validated sample is still available. */
typedef struct OspreyLogicalAccess {
    uint64_t pc;
    OspreyChunk chunk;
    uint32_t dynamic_count;
    uint32_t sample_support;
} OspreyLogicalAccess;

typedef struct OspreyInsnChunkRelation {
    uint64_t pc;
    OspreyChunk chunk;
} OspreyInsnChunkRelation;

typedef struct OspreyChunkRelation {
    OspreyChunk chunk;
} OspreyChunkRelation;

typedef struct OspreyInsnRegionRelation {
    uint64_t pc;
    OspreyRegionId region;
} OspreyInsnRegionRelation;

typedef struct OspreyInsnRegionAddressRelation {
    uint64_t pc;
    OspreyRegionId region;
    OspreyAddress address;
    uint32_t count;
} OspreyInsnRegionAddressRelation;

typedef struct OspreyAllocRelation {
    uint64_t site_pc;
    uint64_t size;
} OspreyAllocRelation;

typedef enum OspreyRelationHintKind {
    OSPREY_RELATION_DATA_FLOW = 0,
    OSPREY_RELATION_UNIFIED_ACCESS = 1,
    OSPREY_RELATION_POINTS_TO = 2,
} OspreyRelationHintKind;

typedef struct OspreyHintRelation {
    OspreyAddress a1;
    OspreyAddress a2;
    int64_t size;
    uint8_t kind;              /* OspreyRelationHintKind */
    uint8_t reserved[7];
    uint64_t witness_count;
} OspreyHintRelation;

/* R01-R12 are separate owned arrays even when their record layouts
 * coincide.  The indexes are parent-local accelerators only; canonical
 * output is always produced from the sorted relation arrays. */
typedef struct OspreyRelations OspreyRelations;
struct OspreyRelations {
    GArray *logical_accesses;
    GArray *r01_accessed;
    GArray *r02_accessed;
    GArray *r03_single_chunk;
    GArray *r04_multi_chunk;
    GArray *r05_high_address;
    GArray *r06_low_address;
    GArray *r07_most_frequent;
    GArray *r08_constant_alloc;
    GArray *r09_alloc_unit;
    GArray *r10_data_flow;
    GArray *r11_unified_access;
    GArray *r12_points_to;

    GHashTable *access_by_pc_region;
    GHashTable *access_by_chunk;
    GHashTable *access_by_pc_chunk;
    GHashTable *alloc_by_site;
    GHashTable *base_by_address;
    GHashTable *points_by_chunk;
};

/* Explicit scalar helpers used by Stage 3.1 and its focused tests. */
bool osprey_relation_same_region(const OspreyRegionId *a,
                                 const OspreyRegionId *b);
bool osprey_relation_offset(const OspreyAddress *a,
                            const OspreyAddress *b, int64_t *out);
bool osprey_relation_adjacent_chunk(const OspreyChunk *a,
                                    const OspreyChunk *b);
bool osprey_relation_overlapping_chunk(const OspreyChunk *a,
                                      const OspreyChunk *b);
bool osprey_relation_addr_difference_gcd(const OspreyAddress *addresses,
                                         size_t count,
                                         const OspreyRegionId *region,
                                         int64_t *out);
bool osprey_relation_size_difference_gcd(const uint64_t *sizes,
                                         size_t count, uint64_t *out);

OspreyKey osprey_logical_access_key(uint64_t pc, const OspreyChunk *chunk);
bool osprey_logical_access_equal(const OspreyLogicalAccess *a,
                                 const OspreyLogicalAccess *b);
gint osprey_logical_access_compare(gconstpointer a, gconstpointer b);

OspreyStatus osprey_relations_build(OspreyContext *ctx);
void osprey_relations_free(OspreyRelations *relations);
void osprey_relations_dump(const OspreyRelations *relations, FILE *out);

/* ------------------------------------------------------------------ */
/* Origin shadows (per-CPU, process-local; never shared)               */
/* ------------------------------------------------------------------ */

/* Stage 2.3 address channel: a register holds a canonical address.
 * Every valid Stage 2.3 origin is pointer-width
 * (width == sizeof(target_ulong)); heap origins carry the authoritative
 * provenance identity pair.  producer_pc is main-image-relative. */
typedef struct OspreyAddressOrigin {
    uint8_t valid;
    uint8_t width;             /* sizeof(target_ulong) when valid */
    uint8_t reserved[6];
    target_ulong concrete_value; /* value-consistency check */
    OspreyAddress canonical;     /* region + signed offset */
    uint64_t prov_object_id;     /* heap origins: provenance identity
                                  * (object_id, generation) */
    uint32_t prov_generation;
    uint32_t reserved2;
    uint64_t producer_pc;        /* normalized producer instruction */
} OspreyAddressOrigin;

/* Stage 2.4 value channel: a register holds a concrete value loaded
 * from a canonical memory chunk.  Every valid Stage 2.4 VALUE origin
 * carries the source memory width (1/2/4/8), the complete post-load
 * architectural GPR value, and the exact canonical source chunk.
 * Deliberately no producer PC or heap generation: F03 describes a
 * historical successful load-to-store flow; the source chunk was
 * validated while its region instance was live. */
typedef struct OspreyValueOrigin {
    uint8_t valid;
    uint8_t width;                 /* source memory width: 1, 2, 4, or 8 */
    uint8_t reserved[6];
    target_ulong concrete_value;   /* architectural GPR value after load */
    OspreyChunk source;            /* exact canonical source chunk */
} OspreyValueOrigin;

typedef struct OspreyRegisterOrigins {
    OspreyAddressOrigin address;
    OspreyValueOrigin value;
} OspreyRegisterOrigins;

/* Sparse aligned memory shadow: ADDRESS slots retained through Stage 2.4;
 * VALUE origins are register-local load history and need no memory shadow. */
typedef struct OspreyMemAddressOrigin {
    uint8_t valid;
    uint8_t width;             /* sizeof(target_ulong) when valid */
    uint8_t reserved[6];
    OspreyAddress canonical;
    target_ulong concrete_value;
    uint64_t prov_object_id;
    uint32_t prov_generation;
    uint32_t reserved2;
} OspreyMemAddressOrigin;

/* Pre-access effective-address snapshot (taken at set_ea time; the
 * base/index registers may be overwritten by the access itself, e.g.
 * mov (%rax),%rax, so F02 selection must use the pre-access origins).
 * base_reg/index_reg retain -1 (absent) and -2 (RIP-relative) exactly;
 * they are never repacked into bytes. */
typedef struct OspreyEASnapshot {
    uint8_t valid;
    uint8_t reserved[7];
    int32_t base_reg;
    int32_t index_reg;
    int32_t scale;
    int64_t disp;
    target_ulong base_val;
    target_ulong index_val;
    OspreyAddressOrigin base_origin;
    OspreyAddressOrigin index_origin;
} OspreyEASnapshot;

#define OSPREY_SHADOW_ALIGN 8

#define OSPREY_MAX_PENDING_HELPER_INTERVALS 64

typedef struct OspreyPendingHelperInterval {
    target_ulong addr;
    target_ulong size;
    target_ulong pc;
    uint32_t op_class;
    uint32_t interval_policy;
    uint32_t producer_id;
    uint8_t is_store;
    uint8_t reserved[3];
} OspreyPendingHelperInterval;

typedef struct OspreyCpuOriginState {
    OspreyRegisterOrigins regs[CPU_NB_REGS];
    /* Aligned native-width memory-shadow hash table.  Key = guest
     * address (aligned slot); value = OspreyMemAddressOrigin*. */
    GHashTable *mem_slots;
    /* Pending effective-address metadata (set before the guest access,
     * consumed after it succeeds). */
    OspreyEASnapshot ea;
    /* Address-mode state of the current instruction (aflags | (override
     * + 1) << 8) recorded by helper_sem_set_ea / helper_sem_mem_access.
     * The F01 eligibility gate (aflag == MO_64 && override < 0) is
     * consumer-side policy in helper_sem_mem_access; push/pop emit no
     * set_ea, so the mem-access event carries the mode itself. */
    uint32_t ea_mode;
    /* Pending raw transfer PC for the two-helper LEA sequence: QEMU
     * 4.1.1 helper declarations stop at six total arguments, so
     * helper_sem_set_pc records the instruction PC immediately before
     * sem_reg_lea / sem_reg_lea_dyn consume and clear it. */
    target_ulong pending_transfer_pc;
    uint8_t pending_transfer_pc_valid;
    uint8_t reserved2[7];
    /* Helper-backed multipart accesses are committed only after their
     * final constituent succeeds.  A fault or producer-family change
     * between parts therefore cannot publish a partial F01 aggregate. */
    OspreyPendingHelperInterval pending_helper[
        OSPREY_MAX_PENDING_HELPER_INTERVALS];
    uint32_t pending_helper_count;
} OspreyCpuOriginState;

/* ------------------------------------------------------------------ */
/* Shared run (fixed layout, no pointers)                              */
/* ------------------------------------------------------------------ */

#define OSPREY_SHARED_VERSION 10u

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
bool osprey_address_origin_live(const OspreyAddressOrigin *o);

/* Exact canonical chunk resolution for an interval (osprey-facts.c).
 * Rejects zero size, addr+size-1 wrap, start/end points outside
 * modeled regions, endpoints in different region identities,
 * nonconsecutive canonical offsets, and offsets/sizes not exactly
 * representable in the fixed record.  Both endpoints are resolved, not
 * just the start.  Used for VALUE creation, ordinary F03/F04
 * destinations, modeled F03, and canonical pointer-cell chunks. */
bool osprey_chunk_of_interval(CPUArchState *env, target_ulong addr,
                              target_ulong size, OspreyChunk *out);
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
    /* Parent-local F01 projection used only by Stage 3.1 relations.
     * Full class/direction F01 rows remain in access_facts. */
    GArray *logical_access_facts; /* OspreyLogicalAccess */
    OspreyRelations *relations;   /* rebuilt transactionally for analysis */

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
    /* Last successfully computed Stage-4 base log partition.  This is
     * diagnostic/test state; failed exact transactions leave it unchanged. */
    double last_exact_logz;

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

typedef enum OspreyGraphStage {
    OSPREY_GRAPH_BASE_CA = 1,
    OSPREY_GRAPH_SECONDARY = 2,
} OspreyGraphStage;

typedef enum OspreyPotentialKind {
    OSPREY_POTENTIAL_IMPLICATION = 1,
    OSPREY_POTENTIAL_PRIOR = 2,
    OSPREY_POTENTIAL_HARD_FALSE = 3,
} OspreyPotentialKind;

/* Predicate kinds (P01-P10 of the reference).  Each concrete predicate
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

/* Accepted signed canonical payload order shared by Stage 3 selection/dumps
 * and Stage 4 local-ID assignment. */
int osprey_var_payload_compare(uint8_t kind, const OspreyVarPayload *a,
                               const OspreyVarPayload *b);

typedef struct OspreyVar {
    uint32_t id;                   /* stable ordinal into ctx->graph->vars */
    uint8_t kind;                  /* OspreyPredicateKind */
    uint8_t hard_false;            /* CB06-style hard constraint */
    uint8_t region_limit_hit;      /* per-region candidate cap exceeded */
    uint8_t reserved;
    uint64_t direct_support;       /* saturated merged proposal evidence */
    uint64_t source_rule_bits;     /* OspreyRuleCode bitset, Stage 3 */
    double prior;                  /* maximum exact proposal prior */
    double belief;                 /* current marginal (Stages 4/5 fill) */
    OspreyVarPayload payload;
} OspreyVar;

typedef struct OspreyInternResult {
    uint32_t id;                   /* UINT32_MAX on rejection */
    bool inserted;                 /* false for duplicates and rejection */
} OspreyInternResult;

typedef struct OspreyFactorResult {
    OspreyStatus status;
    uint32_t id;                   /* UINT32_MAX on rejection */
    bool inserted;                 /* false for duplicates and rejection */
} OspreyFactorResult;

typedef struct OspreyFactorBatchResult {
    OspreyStatus status;
    uint32_t inserted;             /* exact newly inserted factor count */
} OspreyFactorBatchResult;

/* Candidate evidence is collected before interning so cap selection is
 * independent of witness/input order. */
typedef struct OspreyCandidateProposal {
    uint8_t predicate_kind;
    OspreyVarPayload payload;
    uint64_t direct_support;
    double prior;
    uint16_t source_rule;
} OspreyCandidateProposal;

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
    OSPREY_RULE_CD10, OSPREY_RULE_CD11,
    OSPREY_RULE_COUNT,
} OspreyRuleCode;

/* One instantiated rule instance: a factor over semantic variables.
 * Prior factors have one variable and head_idx == 0.  Implications keep
 * their printed antecedent order and head position.  Hard-false factors
 * have head_idx == UINT16_MAX and no probability semantics. */
typedef struct OspreyFactor {
    uint32_t id;
    uint16_t rule;                 /* OspreyRuleCode */
    uint16_t head_idx;             /* prior=0; hard-false=UINT16_MAX */
    uint8_t negative;              /* explicit rule polarity metadata */
    uint8_t stage;                 /* OspreyGraphStage */
    uint8_t potential_kind;        /* OspreyPotentialKind */
    uint8_t reserved;
    double p;                      /* exact target-true probability */
    uint32_t num_vars;
    uint32_t *var_ids;             /* semantic order, never sorted */
} OspreyFactor;

/* Candidate/limit accounting per (kind, region). */
typedef struct OspreyKindRegionCount {
    uint64_t kept;
    uint64_t dropped;
} OspreyKindRegionCount;

typedef struct OspreyRegionExtent {
    OspreyRegionId region;
    int64_t lo;
    int64_t hi;                    /* exclusive; lo <= hi */
} OspreyRegionExtent;

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
    GArray *extents;               /* sorted immutable candidate bounds */
    bool extents_built;             /* facts were snapshotted into extents */
    uint8_t construction_stage;    /* OspreyGraphStage for legacy rule calls */
    /* union-find over vars (component partition for inference) */
    uint32_t *uf_parent;
    uint32_t uf_size;
    uint64_t hint_instances;       /* total R10-R12 hint instances */
    uint64_t limit_rows;           /* [osprey] [limit] rows emitted */
    uint64_t cd04_extensions;      /* CD04 closure extensions */
    /* Raw candidate-proposal rows submitted by each Stage-3 source rule;
     * used for deterministic acceptance diagnostics. */
    uint64_t candidate_proposals[OSPREY_RULE_COUNT];
};

/* Stage 3 base graph entry: current candidate/factor construction over
 * the deterministic relation result.  It does not solve anything. */
OspreyStatus osprey_stage3_base(OspreyContext *ctx);

/* Complete deterministic Stage 3 construction.  This builds the accepted
 * relations, direct candidates, CC/CD factors, and static closure without
 * invoking inference or decoding. */
OspreyStatus osprey_stage3_build(OspreyContext *ctx);

/* Pure CC07 compiler used by the later belief-dependent closure.  All
 * candidate IDs are explicit, selected, and valid in the immutable extent
 * catalog; this function never consults beliefs. */
OspreyStatus osprey_compile_cc07(OspreyContext *ctx,
                                 uint32_t primitive_id,
                                 uint32_t unfoldable_id,
                                 uint32_t foldable_id,
                                 uint32_t folded_primitive_id);

/* Ownership: free a factor graph or decoded model (osprey-rules.c /
 * osprey-decode.c). */
OspreyGraph *osprey_graph_new(void);
void osprey_graph_free(OspreyGraph *g);
void osprey_model_free(OspreyModel *m);

/* Stage 3 secondary construction: all fact- and candidate-driven CC/CD
 * rules plus the static CB02-CB09 closure.  Belief-dependent folding (CC07)
 * is deferred to the Stage 5 dynamic closure. */
OspreyStatus osprey_stage3_secondary(OspreyContext *ctx);

/* Stage 4.1 exact-base projection.  The projection owns local IDs,
 * factor references, and CA-only connectivity; it never aliases graph
 * storage or mutates graph beliefs. */
typedef struct OspreyExactFactorRef {
    uint32_t graph_factor_id;
    uint32_t num_vars;
    uint32_t local_vars[OSPREY_FACTOR_MAX_ARITY];
} OspreyExactFactorRef;

typedef struct OspreyExactComponent {
    GArray *local_vars;   /* uint32_t, canonical local variable IDs */
    GArray *factor_refs;  /* uint32_t indexes into OspreyExactBase */
} OspreyExactComponent;

typedef struct OspreyExactBase {
    GArray *graph_var_ids; /* local variable ID -> production graph ID */
    uint32_t *local_by_graph; /* production graph ID -> local ID or UINT32_MAX */
    uint32_t graph_var_count;
    GArray *factor_refs;   /* OspreyExactFactorRef */
    GPtrArray *components; /* OspreyExactComponent* */
} OspreyExactBase;

OspreyStatus osprey_exact_base_build(OspreyContext *ctx,
                                     OspreyExactBase **out);
void osprey_exact_base_free(OspreyExactBase *base);

/* Stage 4.2 deterministic bounded junction-tree topology.  All records
 * below are temporary, owned by OspreyExactTopology, and retain local IDs
 * rather than pointers into the production graph. */
typedef struct OspreyExactClique {
    uint32_t id;                 /* canonical topology ordinal */
    GArray *local_vars;          /* uint32_t, sorted canonical local IDs */
    GArray *factor_refs;         /* uint32_t indexes into exact base refs */
    uint64_t assignment_cells;   /* checked 2^|local_vars| */
} OspreyExactClique;

typedef struct OspreyExactTreeEdge {
    uint32_t left;               /* canonical endpoint, left < right */
    uint32_t right;
    uint32_t parent;             /* rooted after the tree is selected */
    uint32_t child;
    GArray *separator;           /* uint32_t, exact sorted intersection */
    uint64_t separator_cells;    /* checked 2^|separator| */
} OspreyExactTreeEdge;

typedef struct OspreyExactTopologyComponent {
    uint32_t base_component;     /* index into OspreyExactBase::components */
    GArray *local_vars;          /* copied canonical component variables */
    GArray *elimination_order;   /* uint32_t local IDs, min-fill order */
    GPtrArray *elimination_cliques; /* OspreyExactClique*, one per step */
    GPtrArray *cliques;          /* OspreyExactClique*, maximal canonical */
    GArray *tree_edges;          /* OspreyExactTreeEdge */
    uint32_t root_clique;        /* canonical root, always 0 when nonempty */
    uint32_t max_clique_vars;
    uint64_t assignment_cells;   /* sum over maximal cliques */
    uint64_t separator_cells;    /* sum over both directed messages */
    uint64_t table_bytes;        /* assignment + directed separator tables */
} OspreyExactTopologyComponent;

typedef struct OspreyExactTopology {
    GPtrArray *components;       /* OspreyExactTopologyComponent* */
    GArray *factor_owner;        /* uint32_t flattened canonical clique ID */
    uint32_t variable_count;
    uint32_t factor_count;
    uint64_t clique_count;
    uint64_t max_clique_vars;
    uint64_t table_bytes;        /* checked sum over serial components */
    uint64_t max_component_table_bytes;
} OspreyExactTopology;

OspreyStatus osprey_exact_topology_build(
    OspreyContext *ctx, const OspreyExactBase *base,
    OspreyExactTopology **out);
void osprey_exact_topology_free(OspreyExactTopology *topology);
bool osprey_exact_topology_validate(
    const OspreyContext *ctx, const OspreyExactBase *base,
    const OspreyExactTopology *topology);

/* Stage 4.3 entrypoint.  It builds and validates the bounded topology,
 * computes exact base marginals in temporary workspaces, and publishes
 * beliefs only after every component succeeds. */
OspreyStatus osprey_stage4_exact(OspreyContext *ctx);

/* Test-only deterministic allocation fault injection.  A negative value
 * disables the hook; zero rejects the next exact-numeric allocation. */
void osprey_exact_test_set_alloc_fail_after(int64_t allocations);

/* Stage 4.3 numerical primitives.  These accept finite values or exact
 * -INFINITY only and preserve hard zero support. */
bool osprey_exact_logaddexp(double left, double right, double *out);
bool osprey_exact_log_normalize(double *table, size_t count,
                                double *log_norm);

/* Stages 4/5 inference (osprey-infer.c): Stage 4 topology followed by the
 * still-untrusted secondary BP path. */
OspreyStatus osprey_infer(OspreyContext *ctx);

/* Shared graph builders (osprey-graph.c); used by Stage 3 construction
 * and the Stage 5 dynamic closure. */
OspreyKey osprey_var_key(uint8_t kind, const OspreyVarPayload *payload);
OspreyInternResult osprey_intern_var(OspreyContext *ctx, uint8_t kind,
                                     const OspreyVarPayload *payload);

/* Existing rule compilers use the base-stage convenience form.  It infers
 * PRIOR for one-variable calls and IMPLICATION otherwise, while honoring
 * the graph's current construction stage. */
OspreyFactorResult osprey_factor_add(OspreyContext *ctx, uint16_t rule,
                                     uint16_t head_idx, bool negative,
                                     double p, const uint32_t *var_ids,
                                     uint32_t num_vars);
/* Explicit Stage-3 form used by focused graph tests and future compilers. */
OspreyFactorResult osprey_factor_add_ex(OspreyContext *ctx, uint16_t rule,
                                        uint8_t stage, uint8_t potential_kind,
                                        uint16_t head_idx, bool negative,
                                        double p, const uint32_t *var_ids,
                                        uint32_t num_vars);
OspreyFactorResult osprey_factor_add_prior(OspreyContext *ctx, uint16_t rule,
                                           uint8_t stage, bool negative,
                                           double p, uint32_t head_id);
OspreyFactorResult osprey_factor_add_implication(
    OspreyContext *ctx, uint16_t rule, uint8_t stage, bool negative, double p,
    const uint32_t *antecedent_ids, uint32_t num_antecedents,
    uint32_t head_id);
OspreyFactorResult osprey_factor_add_hard_false(OspreyContext *ctx,
                                                uint16_t rule, uint8_t stage,
                                                uint32_t var_id);
OspreyFactorBatchResult osprey_factor_add_bidirectional(
    OspreyContext *ctx, uint16_t rule, uint8_t stage, bool negative, double p,
    uint32_t left_id, uint32_t right_id);
OspreyFactorBatchResult osprey_factor_add_conjunction_bidirectional(
    OspreyContext *ctx, uint16_t rule, uint8_t stage, bool negative, double p,
    const uint32_t *antecedent_ids, uint32_t num_antecedents,
    uint32_t head_id);
OspreyFactorBatchResult osprey_factor_add_multi_head(
    OspreyContext *ctx, uint16_t rule, uint8_t stage, bool negative, double p,
    const uint32_t *antecedent_ids, uint32_t num_antecedents,
    const uint32_t *head_ids, uint32_t num_heads);
void osprey_graph_set_stage(OspreyGraph *graph, uint8_t stage);
uint32_t osprey_graph_component_count(const OspreyGraph *graph);

static inline uint32_t osprey_intern_var_id(OspreyContext *ctx, uint8_t kind,
                                            const OspreyVarPayload *payload)
{
    return osprey_intern_var(ctx, kind, payload).id;
}

/* Deterministic candidate proposal selection and exact cap accounting. */
OspreyStatus osprey_candidate_select(OspreyContext *ctx,
                                     const OspreyCandidateProposal *proposals,
                                     size_t count);

/* Pure generic potential evaluator shared with inference and tests. */
bool osprey_factor_log_weight(const OspreyFactor *factor,
                              const uint8_t *assignment,
                              double *log_weight);

/* Canonical Stage-3 graph dump.  The path and FILE forms are intentionally
 * explicit so tests do not depend on environment configuration. */
bool osprey_graph_dump(const OspreyContext *ctx, const char *path);
bool osprey_graph_dump_file(const OspreyContext *ctx, FILE *out);

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
