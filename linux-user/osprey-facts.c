/*
 * OSPREY fact collection: runtime region canonicalization, per-sample
 * fact aggregation, address/value origin state, and F01-F06 insertion.
 *
 * Child side: helpers called from translated code write fixed-layout
 * records into the shared run.  Parent side: osprey_parent_merge_sample
 * merges a completed sample into the committed context tables.
 *
 * Collection contract (OSPREY_IMPLEMENTATION_PLAN.md §8):
 *  - hooks commit only after the guest access succeeds;
 *  - sample_support increments at most once per committed sample;
 *  - dynamic_count retains R07's frequency information but is never
 *    used directly as p_k;
 *  - every value-consistency failure invalidates the origin instead of
 *    guessing; no nearest-number fallbacks.
 */

#include "osprey.h"
#include "osprey-internal.h"
#include "sem-events.h"
#include "provenance.h"
/* Origin shadow register invalidation (defined below; used by the
 * stack hooks above). */
static void origin_invalidate_reg(CPUArchState *env, int reg);

#include "qemu/thread.h"
#include "snapshot.h"

#include <stdlib.h>
#include <string.h>

/* Per-sample shared sink and its insert mutex (used by the store/copy
 * hooks above and the allocation-instance section below). */
static OspreySharedRun *g_shared_run = NULL;
static QemuMutex g_shared_mutex;
static bool g_shared_mutex_init = false;

/* ------------------------------------------------------------------ */
/* Fact hashes and equality                                            */
/* ------------------------------------------------------------------ */

/* Full-field equality: a hash is only a bucket selector; identity is the
 * struct itself.  Never compare packed keys. */
static bool eq_region(const OspreyRegionId *a, const OspreyRegionId *b) {
    return a->kind == b->kind && a->code_image_id == b->code_image_id &&
           a->site_offset == b->site_offset;
}

static bool eq_addr(const OspreyAddress *a, const OspreyAddress *b) {
    return a->offset == b->offset && eq_region(&a->region, &b->region);
}

static bool eq_chunk(const OspreyChunk *a, const OspreyChunk *b) {
    return a->size == b->size && eq_addr(&a->address, &b->address);
}

static uint64_t fact_hash_mix(uint64_t hash, uint64_t value) {
    return hash ^ (value + 0x9e3779b97f4a7c15ULL +
                   (hash << 6) + (hash >> 2));
}

uint64_t osprey_access_hash(const OspreyAccessFact *f) {
    OspreyKey k = osprey_chunk_key(&f->chunk);
    k.tag = 0x414343ULL; /* "ACC" */
    k.w[3] = f->pc;
    k.w[4] = f->is_store;
    k.w[5] = f->op_class;
    k.w[6] = (uint64_t)f->chunk.address.offset;
    k.w[7] = f->chunk.size;
    return osprey_key_hash(&k);
}
bool osprey_access_eq(const OspreyAccessFact *a, const OspreyAccessFact *b) {
    return a->pc == b->pc && a->is_store == b->is_store &&
           a->op_class == b->op_class &&
           eq_chunk(&a->chunk, &b->chunk);
}

static bool access_fact_before(const OspreyAccessFact *a,
                               const OspreyAccessFact *b) {
#define CMP(_field) do { \
        if (a->_field != b->_field) return a->_field < b->_field; \
    } while (0)
    CMP(pc);
    CMP(is_store);
    CMP(op_class);
    CMP(chunk.address.region.kind);
    CMP(chunk.address.region.site_offset);
    CMP(chunk.address.offset);
    CMP(chunk.size);
#undef CMP
    return false;
}

uint64_t osprey_base_hash(const OspreyBaseFact *f) {
    OspreyKey k = osprey_chunk_key(&f->chunk);
    k.tag = 0x425345ULL; /* "BSE" */
    uint64_t hash = osprey_key_hash(&k);
    hash = fact_hash_mix(hash, f->pc);
    hash = fact_hash_mix(hash, (uint64_t)f->base.offset);
    hash = fact_hash_mix(hash, (uint64_t)f->base.region.kind);
    hash = fact_hash_mix(hash, f->base.region.site_offset);
    hash = fact_hash_mix(hash, f->prov_object_id);
    hash = fact_hash_mix(hash, f->prov_generation);
    return hash;
}
bool osprey_base_eq(const OspreyBaseFact *a, const OspreyBaseFact *b) {
    return a->pc == b->pc && eq_chunk(&a->chunk, &b->chunk) &&
           eq_addr(&a->base, &b->base) &&
           a->prov_object_id == b->prov_object_id &&
           a->prov_generation == b->prov_generation;
}

/* Canonical base rows sort by their printed fields.  Signed offsets are
 * printed as two's-complement hexadecimal, so compare their uint64_t
 * representations rather than their signed numeric values. */
static gint osprey_base_dump_cmp(gconstpointer ap, gconstpointer bp) {
    const OspreyBaseFact *a = ap;
    const OspreyBaseFact *b = bp;
#define CMP_FIELD(_a, _b) do { \
        uint64_t av = (uint64_t)(_a); \
        uint64_t bv = (uint64_t)(_b); \
        if (av != bv) return av < bv ? -1 : 1; \
    } while (0)
    CMP_FIELD(a->pc, b->pc);
    CMP_FIELD(a->chunk.address.region.kind,
              b->chunk.address.region.kind);
    CMP_FIELD(a->chunk.address.region.site_offset,
              b->chunk.address.region.site_offset);
    CMP_FIELD(a->chunk.address.offset, b->chunk.address.offset);
    CMP_FIELD(a->chunk.size, b->chunk.size);
    CMP_FIELD(a->base.region.kind, b->base.region.kind);
    CMP_FIELD(a->base.region.site_offset, b->base.region.site_offset);
    CMP_FIELD(a->base.offset, b->base.offset);
    CMP_FIELD(a->prov_object_id, b->prov_object_id);
    CMP_FIELD(a->prov_generation, b->prov_generation);
    CMP_FIELD(a->producer_pc, b->producer_pc);
    CMP_FIELD(a->sample_support, b->sample_support);
#undef CMP_FIELD
    return 0;
}

uint64_t osprey_copy_hash(const OspreyCopyFact *f) {
    OspreyKey k = osprey_chunk_key(&f->source);
    k.tag = 0x435059ULL; /* "CPY" */
    uint64_t hash = osprey_key_hash(&k);
    hash = fact_hash_mix(hash,
                         (uint64_t)f->destination.address.region.kind);
    hash = fact_hash_mix(hash, f->destination.address.region.site_offset);
    hash = fact_hash_mix(hash, (uint64_t)f->destination.address.offset);
    hash = fact_hash_mix(hash, f->destination.size);
    return hash;
}
bool osprey_copy_eq(const OspreyCopyFact *a, const OspreyCopyFact *b) {
    return eq_chunk(&a->source, &b->source) &&
           eq_chunk(&a->destination, &b->destination);
}

/* Canonical copy rows sort by every printed field in printed order:
 * src kind, src site, src offset (two's-complement hex order), src
 * size, dst kind, dst site, dst offset, dst size, support. */
static gint osprey_copy_dump_cmp(gconstpointer ap, gconstpointer bp) {
    const OspreyCopyFact *a = ap;
    const OspreyCopyFact *b = bp;
#define CMP(_field) do { \
        uint64_t av = (uint64_t)(a->_field); \
        uint64_t bv = (uint64_t)(b->_field); \
        if (av != bv) return av < bv ? -1 : 1; \
    } while (0)
    CMP(source.address.region.kind);
    CMP(source.address.region.site_offset);
    CMP(source.address.offset);
    CMP(source.size);
    CMP(destination.address.region.kind);
    CMP(destination.address.region.site_offset);
    CMP(destination.address.offset);
    CMP(destination.size);
    CMP(sample_support);
#undef CMP
    return 0;
}

uint64_t osprey_points_hash(const OspreyPointsToFact *f) {
    OspreyKey k = osprey_chunk_key(&f->pointer_chunk);
    k.tag = 0x504E54ULL; /* "PNT" */
    uint64_t hash = osprey_key_hash(&k);
    hash = fact_hash_mix(hash, (uint64_t)f->target.region.kind);
    hash = fact_hash_mix(hash, f->target.region.site_offset);
    hash = fact_hash_mix(hash, (uint64_t)f->target.offset);
    return hash;
}
bool osprey_points_eq(const OspreyPointsToFact *a, const OspreyPointsToFact *b) {
    return eq_chunk(&a->pointer_chunk, &b->pointer_chunk) &&
           eq_addr(&a->target, &b->target);
}

/* Canonical points rows sort by every printed field in printed order:
 * cell kind, cell site, cell offset, cell size, target kind, target
 * site, target offset, support, weak-numeric.  Signed offsets print as
 * two's-complement hex, so compare their uint64_t forms. */
static gint osprey_points_dump_cmp(gconstpointer ap, gconstpointer bp) {
    const OspreyPointsToFact *a = ap;
    const OspreyPointsToFact *b = bp;
#define CMP(_field) do { \
        uint64_t av = (uint64_t)(a->_field); \
        uint64_t bv = (uint64_t)(b->_field); \
        if (av != bv) return av < bv ? -1 : 1; \
    } while (0)
    CMP(pointer_chunk.address.region.kind);
    CMP(pointer_chunk.address.region.site_offset);
    CMP(pointer_chunk.address.offset);
    CMP(pointer_chunk.size);
    CMP(target.region.kind);
    CMP(target.region.site_offset);
    CMP(target.offset);
    CMP(sample_support);
    CMP(weak_numeric_evidence);
#undef CMP
    return 0;
}

uint64_t osprey_alloc_hash(const OspreyMallocFact *f) {
    uint64_t h = f->site_pc;
    h ^= (uint64_t)f->requested_size + 0x9e3779b97f4a7c15ULL +
         (h << 6) + (h >> 2);
    return h;
}
bool osprey_alloc_eq(const OspreyMallocFact *a, const OspreyMallocFact *b) {
    return a->site_pc == b->site_pc && a->requested_size == b->requested_size;
}

uint64_t osprey_region_instance_hash(const OspreyRegionInstance *f) {
    OspreyKey k = osprey_region_key(&f->region);
    k.tag = 0x524749ULL; /* "RGI" */
    k.w[3] = f->instance_id;
    k.w[4] = f->raw_base;
    k.w[5] = f->prov_object_id;
    k.w[6] = f->prov_generation;
    return osprey_key_hash(&k);
}
bool osprey_region_instance_eq(const OspreyRegionInstance *a,
                               const OspreyRegionInstance *b) {
    return a->instance_id == b->instance_id &&
           a->raw_base == b->raw_base &&
           eq_region(&a->region, &b->region) &&
           a->prov_object_id == b->prov_object_id &&
           a->prov_generation == b->prov_generation;
}

uint64_t osprey_mayarray_hash(const OspreyMayArrayFact *f) {
    OspreyKey k = osprey_addr_key(&f->start);
    k.tag = 0x4D4159ULL; /* "MAY" */
    k.w[3] = f->element_count;
    k.w[4] = f->element_size;
    k.w[5] = f->evidence_kind;
    return osprey_key_hash(&k);
}
bool osprey_mayarray_eq(const OspreyMayArrayFact *a,
                        const OspreyMayArrayFact *b) {
    return eq_addr(&a->start, &b->start) &&
           a->element_count == b->element_count &&
           a->element_size == b->element_size &&
           a->evidence_kind == b->evidence_kind;
}

/* ------------------------------------------------------------------ */
/* Open-addressed table inserts (child side)                           */
/* ------------------------------------------------------------------ */

typedef uint64_t (*HashFn)(const void *);
typedef bool (*VerifyFn)(const void *, const void *);
typedef int (*UpdateFn)(void *dst, const void *src); /* <0 = limit */

/* Per-record updaters (support merge on duplicate).  sample_support is
 * Boolean within one committed sample: a duplicate dynamic observation
 * increments only dynamic/weak counters; parent-side support is
 * accumulated once per unique committed sample. */
static uint32_t sat_add_u32(uint32_t a, uint32_t b) {
    if (b > UINT32_MAX - a) return UINT32_MAX;
    return a + b;
}

static uint64_t sat_add_u64(uint64_t a, uint64_t b) {
    if (b > UINT64_MAX - a) return UINT64_MAX;
    return a + b;
}

static int update_access_fact(void *dst, const void *src) {
    OspreyAccessFact *d = dst;
    const OspreyAccessFact *s = src;
    d->dynamic_count = sat_add_u32(d->dynamic_count, s->dynamic_count);
    if (s->sample_support != 0 && d->sample_support == 0) {
        d->sample_support = 1;
    }
    return 0;
}
static int update_base_fact(void *dst, const void *src) {
    OspreyBaseFact *d = dst;
    const OspreyBaseFact *s = src;
    if (s->sample_support != 0 && d->sample_support == 0) {
        d->sample_support = 1;
    }
    /* Deterministic audit metadata: on a logically equal fact, retain
     * the numerically smallest producer PC (including zero) so
     * prefix/suffix and repeated-path order cannot alter the dump.
     * Logical F02 identity never includes producer_pc. */
    if (s->producer_pc < d->producer_pc) {
        d->producer_pc = s->producer_pc;
    }
    return 0;
}
static int update_copy_fact(void *dst, const void *src) {
    OspreyCopyFact *d = dst;
    const OspreyCopyFact *s = src;
    if (s->sample_support != 0 && d->sample_support == 0) {
        d->sample_support = 1;
    }
    return 0;
}
static int update_points_fact(void *dst, const void *src) {
    OspreyPointsToFact *d = dst;
    const OspreyPointsToFact *s = src;
    d->weak_numeric_evidence = sat_add_u32(d->weak_numeric_evidence,
                                           s->weak_numeric_evidence);
    if (s->sample_support != 0 && d->sample_support == 0) {
        d->sample_support = 1;
    }
    return 0;
}
static int update_malloc_fact(void *dst, const void *src) {
    OspreyMallocFact *d = dst;
    const OspreyMallocFact *s = src;
    if (s->sample_support != 0 && d->sample_support == 0) {
        d->sample_support = 1;
    }
    return 0;
}
static int update_mayarray_fact(void *dst, const void *src) {
    OspreyMayArrayFact *d = dst;
    const OspreyMayArrayFact *s = src;
    if (s->sample_support != 0 && d->sample_support == 0) {
        d->sample_support = 1;
    }
    return 0;
}
/* Duplicate region instances merge observed bounds (min of raw_min, max
 * of raw_max) so a growing frame updates its shared record in place;
 * sample support stays Boolean within the sample. */
static int update_region_instance(void *dst, const void *src) {
    OspreyRegionInstance *d = dst;
    const OspreyRegionInstance *s = src;
    if (s->sample_support != 0 && d->sample_support == 0) {
        d->sample_support = 1;
    }
    if (s->raw_min < d->raw_min) d->raw_min = s->raw_min;
    if (s->raw_max > d->raw_max) d->raw_max = s->raw_max;
    return 0;
}
/* Census region: per-region unique-chunk counter.  Returns -1 when the
 * per-region chunk limit is exhausted (fail-closed). */
static int census_region_updater(void *dst, const void *src) {
    OspreyCensusRegion *d = dst;
    const OspreyCensusRegion *s = src;
    uint32_t n = sat_add_u32(d->chunk_count, s->chunk_count);
    d->chunk_count = n;
    return 0;
}

static uint32_t *table_used_ptr(OspreySharedRun *run, int table) {
    switch (table) {
    case OSPREY_TABLE_ACCESS: return &run->access_used;
    case OSPREY_TABLE_BASE: return &run->base_used;
    case OSPREY_TABLE_COPY: return &run->copy_used;
    case OSPREY_TABLE_POINTS: return &run->points_used;
    case OSPREY_TABLE_ALLOC: return &run->alloc_used;
    case OSPREY_TABLE_MAYARR: return &run->mayarray_used;
    case OSPREY_TABLE_REGION: return &run->region_used;
    case OSPREY_TABLE_CENSUS_CHUNK: return &run->census_chunk_used;
    default: return &run->census_region_used;
    }
}

static uint32_t table_cap_of(const OspreySharedRun *run, int table) {
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

static size_t table_record_size_of(int table) {
    switch (table) {
    case OSPREY_TABLE_ACCESS:
    case OSPREY_TABLE_PREFIX_ACCESS: return sizeof(OspreyAccessFact);
    case OSPREY_TABLE_BASE:
    case OSPREY_TABLE_PREFIX_BASE: return sizeof(OspreyBaseFact);
    case OSPREY_TABLE_COPY:
    case OSPREY_TABLE_PREFIX_COPY: return sizeof(OspreyCopyFact);
    case OSPREY_TABLE_POINTS:
    case OSPREY_TABLE_PREFIX_POINTS: return sizeof(OspreyPointsToFact);
    case OSPREY_TABLE_ALLOC:
    case OSPREY_TABLE_PREFIX_ALLOC: return sizeof(OspreyMallocFact);
    case OSPREY_TABLE_MAYARR:
    case OSPREY_TABLE_PREFIX_MAYARR: return sizeof(OspreyMayArrayFact);
    case OSPREY_TABLE_REGION:
    case OSPREY_TABLE_PREFIX_REGION: return sizeof(OspreyRegionInstance);
    case OSPREY_TABLE_CENSUS_CHUNK: return sizeof(OspreyCensusChunk);
    default: return sizeof(OspreyCensusRegion);
    }
}

/* Record count a primary table's used counter denotes (occupied open
 * slots, identical for the prefix family). */
static uint32_t table_used_count(const OspreySharedRun *run, int table) {
    if (table >= OSPREY_TABLE_PREFIX_ACCESS) {
        return osprey_run_prefix_used(run, table);
    }
    return *table_used_ptr((OspreySharedRun *)run, table);
}

/* Stage 2.1 census hashes/equality (full-field identity). */
uint64_t osprey_census_chunk_hash(const OspreyCensusChunk *f) {
    OspreyKey k = osprey_chunk_key(&f->chunk);
    return osprey_key_hash(&k);
}
bool osprey_census_chunk_eq(const OspreyCensusChunk *a,
                            const OspreyCensusChunk *b) {
    return eq_chunk(&a->chunk, &b->chunk);
}
uint64_t osprey_census_region_hash(const OspreyCensusRegion *f) {
    OspreyKey k = osprey_region_key(&f->region);
    return osprey_key_hash(&k);
}
bool osprey_census_region_eq(const OspreyCensusRegion *a,
                             const OspreyCensusRegion *b) {
    return eq_region(&a->region, &b->region);
}

/* True when the frozen-prefix peer of a primary table already holds an
 * equal record: the fact is part of both the prefix and the suffix, so
 * it is one union member, not two. */
static bool run_table_has_peer(const OspreySharedRun *run, int table,
                               const void *rec, HashFn hash, VerifyFn eq) {
    int pref = OSPREY_TABLE_PREFIX_ACCESS +
               (table - OSPREY_TABLE_ACCESS);
    if (table < 0 || table >= OSPREY_TABLE_PRIMARY_COUNT) return false;
    uint32_t cap = table_cap_of(run, pref);
    if (cap == 0) return false;
    uint8_t *base = osprey_run_table((OspreySharedRun *)run, pref);
    size_t rec_size = table_record_size_of(pref);
    uint64_t h = hash(rec);
    uint32_t slot = (uint32_t)(h % cap);
    uint32_t step = 1;
    while (step <= cap) {
        uint8_t *ent = base + (size_t)slot * rec_size;
        bool empty = true;
        for (size_t i = 0; i < rec_size; i++) {
            if (ent[i] != 0) {
                empty = false;
                break;
            }
        }
        if (empty) {
            return false;
        }
        if (eq(ent, rec)) {
            return true;
        }
        slot = (slot + step) % cap;
        step++;
    }
    return false;
}

/* Generic insert; return 1 new, 0 duplicate-updated, -1 table full.
 * The `is_primary` flag distinguishes child-writable tables (subject to
 * the total unique-fact cap and census accounting) from read-only
 * prefix tables and counting census tables. */
static int run_table_insert(OspreySharedRun *run, int table, const void *rec,
                            HashFn hash, VerifyFn eq, UpdateFn upd,
                            bool is_primary) {
    uint32_t cap = table_cap_of(run, table);
    uint32_t used = *table_used_ptr(run, table);
    if (cap == 0) {
        goto full;
    }
    uint8_t *base = osprey_run_table(run, table);
    size_t rec_size = table_record_size_of(table);
    uint64_t h = hash(rec);
    uint32_t slot = (uint32_t)(h % cap);
    uint32_t step = 1;
    while (step <= cap) {
        uint8_t *ent = base + (size_t)slot * rec_size;
        bool empty = true;
        for (size_t i = 0; i < rec_size; i++) {
            if (ent[i] != 0) {
                empty = false;
                break;
            }
        }
        if (empty) {
            /* The unique-fact cap applies only to NEW records: a
             * duplicate observation of an already-counted fact (in the
             * suffix or frozen prefix) must never be rejected. */
            bool in_prefix = is_primary && run->prefix_frozen &&
                run_table_has_peer(run, table, rec, hash, eq);
            if (is_primary && !in_prefix &&
                run->total_facts_count >= run->max_facts_cfg) {
                goto full;
            }
            memcpy(ent, rec, rec_size);
            *table_used_ptr(run, table) = used + 1;
            if (is_primary) {
                /* The sample's unique-fact count is the union of the
                 * frozen prefix and the child suffix: a fact that is
                 * already in the frozen prefix (same full-field record)
                 * is not a new union member. */
                if (!in_prefix) {
                    run->total_facts_count++;
                }
            }
            return 1;
        }
        if (eq(ent, rec)) {
            if (upd != NULL) {
                int rc = upd(ent, rec);
                if (rc < 0) {
                    goto full;
                }
            }
            return 0;
        }
        slot = (slot + step) % cap;
        step++;
    }
full:
    run->overflow = 1;
    if (run->first_dropped_kind == 0) {
        run->first_dropped_kind = (uint32_t)table + 1;
        run->first_dropped_hash = hash(rec);
    }
    return -1;
}

/* Dedicated census inserts: count unique chunks per sample (cap
 * max_facts) and unique chunks per region (cap max_chunks_per_region).
 * Returns 1 new, 0 duplicate, -1 limit exhausted (fail-closed). */
static int census_chunk_insert(OspreySharedRun *run, const OspreyChunk *chunk) {
    OspreyCensusChunk cc;
    memset(&cc, 0, sizeof(cc));
    cc.chunk = *chunk;
    return run_table_insert(run, OSPREY_TABLE_CENSUS_CHUNK, &cc,
                            (HashFn)osprey_census_chunk_hash,
                            (VerifyFn)osprey_census_chunk_eq, NULL, false);
}

static int census_region_record_insert(OspreySharedRun *run,
                                       const OspreyCensusRegion *cr) {
    int rc = run_table_insert(run, OSPREY_TABLE_CENSUS_REGION, cr,
                              (HashFn)osprey_census_region_hash,
                              (VerifyFn)osprey_census_region_eq,
                              census_region_updater, false);
    if (rc < 0) return -1;
    /* Per-region unique-chunk limit: a region's census count may not
     * exceed max_chunks_per_region.  The count saturates at UINT32_MAX
     * (the census capacity is derived from the same limit, so a
     * well-formed run cannot overflow the table first); check the
     * count against the configured limit explicitly. */
    if (run->max_chunks_cfg > 0) {
        uint32_t cap = table_cap_of(run, OSPREY_TABLE_CENSUS_REGION);
        uint8_t *base = osprey_run_table(run, OSPREY_TABLE_CENSUS_REGION);
        size_t rec_size = table_record_size_of(OSPREY_TABLE_CENSUS_REGION);
        uint64_t h = osprey_census_region_hash(cr);
        uint32_t slot = (uint32_t)(h % cap);
        uint32_t step = 1;
        while (step <= cap) {
            OspreyCensusRegion *ent = (OspreyCensusRegion *)
                (base + (size_t)slot * rec_size);
            if (osprey_census_region_eq(ent, cr)) {
                if (ent->chunk_count > run->max_chunks_cfg) {
                    run->overflow = 1;
                    if (run->first_dropped_kind == 0) {
                        run->first_dropped_kind =
                            (uint32_t)OSPREY_TABLE_CENSUS_REGION + 1;
                        run->first_dropped_hash = h;
                    }
                    return -1;
                }
                break;
            }
            slot = (slot + step) % cap;
            step++;
        }
    }
    return 0;
}

static int census_region_insert(OspreySharedRun *run,
                                const OspreyRegionId *region) {
    OspreyCensusRegion cr;
    memset(&cr, 0, sizeof(cr));
    cr.region = *region;
    cr.chunk_count = 1;
    return census_region_record_insert(run, &cr);
}

/* Census accounting for a new access fact: count the unique chunk and
 * the chunk's region against their per-sample limits.  Called before
 * the fact insert; a limit exhaustion rejects fail-closed.  The
 * per-region census counts unique chunks per region (capped at
 * max_chunks_per_region), and the global census counts unique chunks
 * per sample (capped at max_facts).  A duplicate dynamic observation of
 * an already-counted chunk does not increment either census. */
static int census_insert_chunk(OspreySharedRun *run, const OspreyChunk *chunk) {
    int rc = census_chunk_insert(run, chunk);
    if (rc < 0) return -1;
    if (rc == 1) {
        /* New unique chunk in this sample: count it in its region. */
        return census_region_insert(run, &chunk->address.region);
    }
    return 0;
}

int osprey_table_insert_access(OspreySharedRun *run, const OspreyAccessFact *f) {
    if (census_insert_chunk(run, &f->chunk) < 0) return -1;
    return run_table_insert(run, OSPREY_TABLE_ACCESS, f,
                            (HashFn)osprey_access_hash,
                            (VerifyFn)osprey_access_eq, update_access_fact,
                            true);
}
int osprey_table_insert_base(OspreySharedRun *run, const OspreyBaseFact *f) {
    if (census_insert_chunk(run, &f->chunk) < 0) return -1;
    return run_table_insert(run, OSPREY_TABLE_BASE, f,
                            (HashFn)osprey_base_hash,
                            (VerifyFn)osprey_base_eq, update_base_fact,
                            true);
}
int osprey_table_insert_copy(OspreySharedRun *run, const OspreyCopyFact *f) {
    if (census_insert_chunk(run, &f->source) < 0) return -1;
    if (census_insert_chunk(run, &f->destination) < 0) return -1;
    return run_table_insert(run, OSPREY_TABLE_COPY, f,
                            (HashFn)osprey_copy_hash,
                            (VerifyFn)osprey_copy_eq, update_copy_fact,
                            true);
}
int osprey_table_insert_points(OspreySharedRun *run, const OspreyPointsToFact *f) {
    if (census_insert_chunk(run, &f->pointer_chunk) < 0) return -1;
    return run_table_insert(run, OSPREY_TABLE_POINTS, f,
                            (HashFn)osprey_points_hash,
                            (VerifyFn)osprey_points_eq, update_points_fact,
                            true);
}
int osprey_table_insert_alloc(OspreySharedRun *run, const OspreyMallocFact *f) {
    return run_table_insert(run, OSPREY_TABLE_ALLOC, f,
                            (HashFn)osprey_alloc_hash,
                            (VerifyFn)osprey_alloc_eq, update_malloc_fact,
                            true);
}
int osprey_table_insert_mayarray(OspreySharedRun *run, const OspreyMayArrayFact *f) {
    return run_table_insert(run, OSPREY_TABLE_MAYARR, f,
                            (HashFn)osprey_mayarray_hash,
                            (VerifyFn)osprey_mayarray_eq, update_mayarray_fact,
                            true);
}
int osprey_table_insert_region(OspreySharedRun *run,
                               const OspreyRegionInstance *f) {
    return run_table_insert(run, OSPREY_TABLE_REGION, f,
                            (HashFn)osprey_region_instance_hash,
                            (VerifyFn)osprey_region_instance_eq,
                            update_region_instance, true);
}

/* Public census inserts (used by tests to drive limit fixtures). */
int osprey_table_insert_census_chunk(OspreySharedRun *run,
                                     const OspreyCensusChunk *f) {
    return run_table_insert(run, OSPREY_TABLE_CENSUS_CHUNK, f,
                            (HashFn)osprey_census_chunk_hash,
                            (VerifyFn)osprey_census_chunk_eq, NULL, false);
}
int osprey_table_insert_census_region(OspreySharedRun *run,
                                      const OspreyCensusRegion *f) {
    return census_region_record_insert(run, f);
}

int osprey_run_iter_next(OspreyRunIter *it, const void **record) {
    if (it == NULL || it->run == NULL || record == NULL) return 0;
    const OspreySharedRun *run = it->run;
    uint8_t *base = osprey_run_table((OspreySharedRun *)run, it->table);
    size_t rec_size = table_record_size_of(it->table);
    uint32_t cap = table_cap_of(run, it->table);
    while (it->slot < cap) {
        uint8_t *rec = base + (size_t)it->slot * rec_size;
        it->slot++;
        bool empty = true;
        for (size_t i = 0; i < rec_size; i++) {
            if (rec[i] != 0) {
                empty = false;
                break;
            }
        }
        if (!empty) {
            *record = rec;
            return 1;
        }
    }
    return 0;
}

/* ------------------------------------------------------------------ */
/* Region resolution                                                   */
/* ------------------------------------------------------------------ */

/* Runtime region catalog (parent- and child-side shared state).  Heap
 * instances are created on successful allocation returns; stack frames
 * on call/return hooks; the global region from elfload registration. */

typedef struct OspreyStackFrame {
    OspreyRegionId region;
    target_ulong entry_sp;
    target_ulong current_sp;
    target_ulong min_sp;
    target_ulong max_sp;   /* observed top; entry_sp for stack frames */
    bool precise;
    uint64_t instance_id;   /* monotonic; distinguishes same-site frames */
} OspreyStackFrame;

/* x86-64 SysV leaf functions may use 128 bytes below RSP without moving
 * the register.  This is the only implicit stack-growth allowance; all
 * other growth must first be observed through an architectural RSP write. */
#define OSPREY_STACK_RED_ZONE 128u

static GArray *g_stack_frames = NULL; /* OspreyStackFrame */
static uint64_t g_next_stack_instance = 1;

/* Sentinel site offset for imprecise frames (callee PC outside the main
 * image).  Such frames are excluded from structural factors. */
#define OSPREY_STACK_IMPRECISE_SITE ((uint64_t)-1)

typedef struct HeapInstance {
    OspreyRegionId region;   /* H_site */
    uint64_t instance_id;
    target_ulong base;
    uint64_t size;
    uint64_t prov_object_id;   /* accepted provenance identity */
    uint32_t prov_generation;
    bool live;
} HeapInstance;

static GArray *g_heap_instances = NULL; /* HeapInstance */
static uint64_t g_next_heap_instance = 1;

/* Region-instance recorder (defined below with the allocation hooks;
 * used earlier by the image-global and stack-frame registration). */
static void record_region_instance(const OspreyRegionId *region,
                                   uint64_t instance_id,
                                   target_ulong raw_base,
                                   uint64_t raw_min,
                                   uint64_t raw_max,
                                   uint64_t prov_object_id,
                                   uint32_t prov_generation);

void osprey_register_image_global(CPUArchState *env, target_ulong base,
                                  target_ulong size) {
    (void)env;
    /* Merge into the main-image writable interval set (image-relative
     * offsets); .data and .bss become one canonical G region. */
    OspreyContext *ctx = osprey_ctx_ref();
    if (ctx != NULL) {
        global_ranges_add(ctx, base, (uint64_t)size);
    }
}

/* Resolve a runtime address to a canonical region.  Returns false when
 * the address is not in any modeled region (libraries, anonymous mmap);
 * never guesses a region from numeric proximity.  When `grow` is true,
 * an access below the observed stack bound extends the frame through
 * the ABI red zone and re-publishes the observed span (F01 collection
 * path only).  When `grow` is false (Stage 2.4 fact-resolution paths:
 * VALUE creation, F03/F04 destinations, pointer cells), the red-zone
 * growth side effect is forbidden: metadata resolution must never
 * mutate frame bounds, and out-of-image accesses must not change the
 * canonical region set. */
static bool osprey_region_of_addr_inner(CPUArchState *env,
                                        target_ulong addr,
                                        OspreyRegionId *region,
                                        int64_t *offset, bool grow) {
    (void)env;
    /* 1. Live heap instances. */
    if (g_heap_instances != NULL) {
        for (guint i = 0; i < g_heap_instances->len; i++) {
            HeapInstance *h = &g_array_index(g_heap_instances, HeapInstance, i);
            if (!h->live) continue;
            if (addr >= h->base && (uint64_t)(addr - h->base) < h->size) {
                *region = h->region;
                *offset = (int64_t)(addr - h->base);
                return true;
            }
        }
    }
    /* 2. Main-image global data. */
    if (osprey_global_of_addr(addr, region, offset)) {
        return true;
    }
    /* 3. Stack frames: innermost live frame first.  Offsets are signed
     * relative to the entry SP (negative below it).  Architectural RSP
     * writes establish the observed lower bound; only the ABI red zone
     * can extend it implicitly. */
    if (g_stack_frames != NULL) {
        for (guint i = g_stack_frames->len; i > 0; i--) {
            OspreyStackFrame *f = &g_array_index(g_stack_frames,
                                                 OspreyStackFrame, i - 1);
            /* Imprecise frames (callee outside the main image) never
             * contribute facts; skip them so no access resolves into
             * their window. */
            if (f->region.site_offset == OSPREY_STACK_IMPRECISE_SITE) {
                continue;
            }
            if (addr >= f->entry_sp) {
                continue;
            }
            if (addr >= f->min_sp) {
                *region = f->region;
                *offset = (int64_t)addr - (int64_t)f->entry_sp;
                return true;
            }
            /* Access below min_sp: grow only through the ABI-defined
             * red zone below the currently observed RSP.  The previous
             * synthetic one-MiB window could assign an unrelated address
             * to the innermost frame and was not an observed bound. */
            target_ulong red_zone_low =
                f->current_sp >= OSPREY_STACK_RED_ZONE
                    ? f->current_sp - OSPREY_STACK_RED_ZONE : 0;
            if (addr >= red_zone_low && addr < f->current_sp) {
                if (!grow) {
                    /* Non-mutating resolution: the address is
                     * structurally inside the frame's red zone, but the
                     * caller forbids extending the observed bounds. */
                    *region = f->region;
                    *offset = (int64_t)addr - (int64_t)f->entry_sp;
                    return true;
                }
                f->min_sp = addr;
                /* Publish the grown bounds into the shared record so
                 * the parent sees the observed span, not a synthetic
                 * extent. */
                record_region_instance(&f->region, f->instance_id,
                                       f->entry_sp, f->min_sp, f->max_sp,
                                       0, 0);
                *region = f->region;
                *offset = (int64_t)addr - (int64_t)f->entry_sp;
                return true;
            }
        }
    }
    return false;
}

/* Public resolver: F01 access path, allowed to grow observed stack
 * bounds through the red zone (Stage 2.3 behavior preserved exactly). */
bool osprey_region_of_addr(CPUArchState *env, target_ulong addr,
                           OspreyRegionId *region, int64_t *offset,
                           bool create) {
    return osprey_region_of_addr_inner(env, addr, region, offset, true);
}

/* Exact canonical chunk resolution for an interval: reject zero size,
 * addr+size-1 wrap, start/end points outside modeled regions, endpoints
 * in different region identities, nonconsecutive canonical offsets,
 * and offsets/sizes not exactly representable in the fixed record.
 * Both endpoints are resolved, not just the start.  Used for VALUE
 * creation, ordinary F03/F04 destinations, modeled F03, and canonical
 * pointer-cell chunks. */
bool osprey_chunk_of_interval(CPUArchState *env, target_ulong addr,
                              target_ulong size, OspreyChunk *out) {
    if (out == NULL || size == 0) {
        return false;
    }
    target_ulong delta = size - 1;
    if (delta > (target_ulong)-1 - addr || delta > INT64_MAX) {
        return false;
    }
    target_ulong end = addr + delta;
    OspreyRegionId rstart, rend;
    int64_t ostart = 0, oend = 0;
    if (!osprey_region_of_addr_inner(env, addr, &rstart, &ostart, false)) {
        return false;
    }
    if (!osprey_region_of_addr_inner(env, end, &rend, &oend, false)) {
        return false;
    }
    if (!eq_region(&rstart, &rend)) {
        return false;
    }
    int64_t expected_end = 0;
    if (!osprey_check_add(ostart, (int64_t)delta, &expected_end) ||
        oend != expected_end) {
        /* Nonconsecutive canonical offsets: the interval is not one
         * contiguous representable span (or the canonical delta
         * overflowed the fixed signed offset). */
        return false;
    }
    if (ostart < 0 && oend >= 0) {
        /* The interval straddles the region anchor (offset 0): a chunk
         * may never cross the anchor with a mixed-sign span.  Fully
         * negative stack spans (below the entry SP) are valid and
         * remain exactly representable in the signed fixed record. */
        return false;
    }
    out->address.region = rstart;
    out->address.offset = ostart;
    out->size = size;
    return true;
}

/* Main-image normalization: map a runtime PC to an image-relative
 * offset, or return false when the PC is outside the image. */
static bool osprey_normalize_pc(target_ulong pc, uint64_t *out) {
    target_ulong image_base = osprey_get_image_base();
    target_ulong image_end = osprey_get_image_end();
    if (image_end <= image_base || pc < image_base || pc >= image_end) {
        return false;
    }
    *out = (uint64_t)(pc - image_base);
    return true;
}

static void stack_seed_rsp_origin(CPUArchState *env,
                                  const OspreyStackFrame *frame,
                                  target_ulong sp) {
    if (frame == NULL || !frame->precise) {
        origin_invalidate_reg(env, R_ESP);
        return;
    }
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    memset(&st->regs[R_ESP], 0, sizeof(st->regs[R_ESP]));
    OspreyAddressOrigin *o = &st->regs[R_ESP].address;
    o->valid = 1;
    o->width = (uint8_t)sizeof(target_ulong);
    o->concrete_value = sp;
    o->canonical.region = frame->region;
    o->canonical.offset = (int64_t)sp - (int64_t)frame->entry_sp;
    /* Precise stack seeds use the normalized callee/entrypoint PC as
     * their producer identity (a real normalized producer offset, not a
     * synthetic sentinel). */
    o->producer_pc = frame->region.site_offset;
}

void osprey_on_call(CPUArchState *env, target_ulong callee_pc,
                    target_ulong entry_sp) {
    if (g_stack_frames == NULL) {
        g_stack_frames = g_array_new(FALSE, FALSE, sizeof(OspreyStackFrame));
    }
    OspreyStackFrame f;
    memset(&f, 0, sizeof(f));
    f.region.kind = OSPREY_REGION_STACK_FUNCTION;
    f.region.code_image_id = 0;
    f.precise = osprey_normalize_pc(callee_pc, &f.region.site_offset);
    if (!f.precise) {
        f.region.site_offset = OSPREY_STACK_IMPRECISE_SITE;
    }
    /* entry_sp is the precise callee-entry RSP: the call hook fires
     * after the return-address push (direct/indirect sites emit it
     * after gen_push_v; the E9 site observes the stub's push), so the
     * passed RSP is the callee entry. */
    f.entry_sp = entry_sp;
    f.current_sp = entry_sp;
    f.min_sp = f.entry_sp;
    f.max_sp = f.entry_sp;
    f.instance_id = g_next_stack_instance++;
    g_array_append_val(g_stack_frames, f);
    /* Stack instance bounds are dynamic; record the entry SP as the raw
     * base with the observed span so the parent can map addresses.
     * Imprecise frames (callee outside the main image) are never
     * recorded: no fact can reference them (their accesses are skipped
     * at PC normalization) and they must not pollute the canonical
     * region set. */
    if (f.precise) {
        record_region_instance(&f.region, f.instance_id, f.entry_sp,
                               f.min_sp, f.max_sp, 0, 0);
    }
    /* Seed the RSP origin: the register holds entry_sp (the hook fires
     * after the return-address push), i.e. the new frame at offset 0.
     * Precise callee entry only — imprecise frames never contribute
     * facts. */
    stack_seed_rsp_origin(env, &f, entry_sp);
}

/* Entrypoint barrier (snapshot/forkserver entry): seed the initial
 * stack frame for the main image when the entrypoint is reached from
 * uninstrumented loader/libc code (no call hook fired for main).
 * Idempotent: creates a precise frame only when no live frame with the
 * same region and entry SP exists; the observed entry SP is the
 * offset-zero anchor.  Fires once per process (parent at the target
 * hit; the child re-executes the entrypoint TB with count target+1). */
void osprey_on_entrypoint(CPUArchState *env, target_ulong pc,
                          target_ulong sp) {
    if (g_stack_frames == NULL) {
        g_stack_frames = g_array_new(FALSE, FALSE, sizeof(OspreyStackFrame));
    }
    OspreyRegionId region;
    memset(&region, 0, sizeof(region));
    region.kind = OSPREY_REGION_STACK_FUNCTION;
    region.code_image_id = 0;
    if (!osprey_normalize_pc(pc, &region.site_offset)) {
        /* Entrypoint outside the main image: nothing to seed. */
        return;
    }
    /* Idempotent: a matching live frame (same region + entry SP) means
     * the entrypoint was already reached (called-patch fixture where
     * main is called from instrumented code, or a re-hit). */
    for (guint i = 0; i < g_stack_frames->len; i++) {
        OspreyStackFrame *f = &g_array_index(g_stack_frames,
                                            OspreyStackFrame, i);
        if (f->region.site_offset == region.site_offset &&
            f->entry_sp == sp) {
            f->current_sp = sp;
            stack_seed_rsp_origin(env, f, sp);
            return;
        }
    }
    OspreyStackFrame f;
    memset(&f, 0, sizeof(f));
    f.region = region;
    f.entry_sp = sp;
    f.current_sp = sp;
    f.min_sp = sp;
    f.max_sp = sp;
    f.precise = true;
    f.instance_id = g_next_stack_instance++;
    g_array_append_val(g_stack_frames, f);
    record_region_instance(&f.region, f.instance_id, f.entry_sp,
                           f.min_sp, f.max_sp, 0, 0);
    /* Seed the RSP origin: the register holds the entry SP (offset
     * zero of the new frame). */
    stack_seed_rsp_origin(env, &f, sp);
}

void osprey_on_ret(CPUArchState *env, target_ulong pc, target_ulong sp) {
    (void)pc;
    if (g_stack_frames == NULL || g_stack_frames->len == 0) {
        origin_invalidate_reg(env, R_ESP);
        return;
    }
    /* A RET always ends the current activation: pop the top frame
     * unconditionally, even when a malformed epilogue leaves the
     * post-pop SP inside it.  Then discard any additional stale frames
     * whose entry lies strictly below the post-pop SP; a frame whose
     * entry is at or above it survives (the caller's entry is its
     * call-site RSP, always at or above the post-pop SP).  A deep
     * library return legitimately lands far below the callers'
     * observed minima, so a frame's minimum never drives the pop. */
    g_array_set_size(g_stack_frames, g_stack_frames->len - 1);
    while (g_stack_frames->len > 0) {
        OspreyStackFrame *top = &g_array_index(g_stack_frames,
                                               OspreyStackFrame,
                                               g_stack_frames->len - 1);
        if (sp <= top->entry_sp) {
            break;
        }
        g_array_set_size(g_stack_frames, g_stack_frames->len - 1);
    }
    /* Re-seed the RSP origin to the caller frame (now top): after the
     * pop, RSP is the call-site RSP (pre-push), i.e. the caller frame
     * at a signed offset.  An imprecise caller (libc) never contributes
     * facts: invalidate instead. */
    if (g_stack_frames->len > 0) {
        OspreyStackFrame *caller = &g_array_index(g_stack_frames,
                                                  OspreyStackFrame,
                                                  g_stack_frames->len - 1);
        if (caller->precise) {
            caller->current_sp = sp;
            stack_seed_rsp_origin(env, caller, sp);
        } else {
            origin_invalidate_reg(env, R_ESP);
        }
    } else {
        origin_invalidate_reg(env, R_ESP);
    }
}

/* RSP update (push/pop/add/sub imm, call): re-derive the RSP origin
 * from the live frame stack.  The innermost precise frame whose entry
 * SP is at or above the new RSP owns the register; offset is signed
 * relative to that entry.  No frame (or only imprecise frames) →
 * invalidate.  This runs after the write-back kill, so the origin is
 * always rebuilt from frame identity, never adjusted incrementally. */
void osprey_on_rsp_update(CPUArchState *env, target_ulong new_sp,
                          target_ulong pc) {
    /* Only in-image RSP writes re-derive the origin: libc frames are
     * imprecise and must never claim a precise frame's identity. */
    uint64_t norm_pc = 0;
    if (!osprey_normalize_pc(pc, &norm_pc)) {
        origin_invalidate_reg(env, R_ESP);
        return;
    }
    if (g_stack_frames != NULL) {
        /* Non-local stack resynchronization: an upward replacement can
         * cross one or more callee entry anchors.  Pop those frames.
         * Downward movement belongs to the current precise activation
         * and grows its observed bound; there is no synthetic depth cap.
         * RET/RET-imm suppress this generic helper in the translator;
         * osprey_on_ret owns their activation pop exactly once. */
        while (g_stack_frames->len > 0) {
            OspreyStackFrame *top = &g_array_index(g_stack_frames,
                                                   OspreyStackFrame,
                                                   g_stack_frames->len - 1);
            if (new_sp <= top->entry_sp) {
                break;
            }
            g_array_set_size(g_stack_frames, g_stack_frames->len - 1);
        }
        for (guint i = g_stack_frames->len; i > 0; i--) {
            OspreyStackFrame *f = &g_array_index(g_stack_frames,
                                                 OspreyStackFrame, i - 1);
            if (f->region.site_offset == OSPREY_STACK_IMPRECISE_SITE) {
                continue;
            }
            if (new_sp <= f->entry_sp) {
                f->current_sp = new_sp;
                /* The frame grows to cover the new RSP position
                 * (prologue sub rsp); publish the grown bounds. */
                if (new_sp < f->min_sp) {
                    f->min_sp = new_sp;
                    record_region_instance(&f->region, f->instance_id,
                                           f->entry_sp, f->min_sp,
                                           f->max_sp, 0, 0);
                }
                /* Re-derive the canonical stack identity from the live
                 * frame and set the producer PC to the normalized write
                 * instruction. */
                {
                    OspreyCpuOriginState *st = osprey_cpu_origin(env);
                    memset(&st->regs[R_ESP], 0,
                           sizeof(st->regs[R_ESP]));
                    OspreyAddressOrigin *o =
                        &st->regs[R_ESP].address;
                    o->valid = 1;
                    o->width = (uint8_t)sizeof(target_ulong);
                    o->concrete_value = new_sp;
                    o->canonical.region = f->region;
                    o->canonical.offset =
                        (int64_t)new_sp - (int64_t)f->entry_sp;
                    o->producer_pc = norm_pc;
                }
                return;
            }
        }
    }
    origin_invalidate_reg(env, R_ESP);
}

/* ------------------------------------------------------------------ */
/* Origin shadows (per-CPU)                                            */
/* ------------------------------------------------------------------ */

/* The origin shadow tracks address-origin and value-origin tags for
 * architectural GPRs plus a sparse aligned native-width memory shadow.
 * Transfer rules are deliberately conservative (see
 * OSPREY_IMPLEMENTATION_PLAN.md §8.3): full-width mov, lea with checked
 * constant offset, and aligned spill/reload with matching bytes.
 * Every other register write invalidates. */

static void origin_invalidate_reg(CPUArchState *env, int reg) {
    if (reg < 0 || reg >= CPU_NB_REGS) return;
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    memset(&st->regs[reg], 0, sizeof(st->regs[reg]));
}

/* Install one validated address origin into `dst`; always clears the
 * destination VALUE channel (explicit two-channel write policy).  The
 * caller must already hold a normalized producer PC. */
static void origin_install_address(CPUArchState *env, int dst,
                                   const OspreyAddress *canonical,
                                   uint64_t prov_object_id,
                                   uint32_t prov_generation,
                                   uint64_t producer_pc,
                                   target_ulong concrete_value) {
    if (dst < 0 || dst >= CPU_NB_REGS) return;
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    memset(&st->regs[dst], 0, sizeof(st->regs[dst]));
    OspreyAddressOrigin *o = &st->regs[dst].address;
    o->valid = 1;
    o->width = (uint8_t)sizeof(target_ulong);
    o->concrete_value = concrete_value;
    o->canonical = *canonical;
    o->prov_object_id = prov_object_id;
    o->prov_generation = prov_generation;
    o->producer_pc = producer_pc;
}

/* Canonical-region identity check for a transfer. */
static bool origin_region_eq(const OspreyRegionId *a,
                             const OspreyRegionId *b) {
    return a->kind == b->kind && a->code_image_id == b->code_image_id &&
           a->site_offset == b->site_offset;
}

static bool origin_address_eq(const OspreyAddressOrigin *a,
                              const OspreyAddressOrigin *b) {
    return a->valid == b->valid && a->width == b->width &&
           a->concrete_value == b->concrete_value &&
           origin_region_eq(&a->canonical.region, &b->canonical.region) &&
           a->canonical.offset == b->canonical.offset &&
           a->prov_object_id == b->prov_object_id &&
           a->prov_generation == b->prov_generation &&
           a->producer_pc == b->producer_pc;
}

/* Invalidate a bad pre-access snapshot only when the architectural
 * register still carries that exact channel.  A successful self-overwriting
 * load may already have installed a newer destination origin. */
static void origin_invalidate_snapshot(CPUArchState *env, int reg,
                                       const OspreyAddressOrigin *snapshot) {
    if (reg < 0 || reg >= CPU_NB_REGS || snapshot == NULL) {
        return;
    }
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    if (origin_address_eq(&st->regs[reg].address, snapshot)) {
        memset(&st->regs[reg].address, 0,
               sizeof(st->regs[reg].address));
    }
}

/* Interpret target-width wrapping subtraction as a signed x86-64 delta
 * without performing overflowing signed subtraction. */
static int64_t origin_wrapped_delta(target_ulong value, target_ulong base) {
    return (int64_t)(target_long)(value - base);
}

/* A live heap ADDRESS origin must still reference the authoritative
 * provenance object: {object_id, generation} live, concrete value
 * within the object or its one-past address, canonical offset equal to
 * the concrete delta, and
 * canonical region matching the object's allocation site.  Conversely,
 * non-heap origins must not carry a provenance identity. */
static bool origin_heap_prov_ok(const OspreyAddressOrigin *o) {
    if (o->canonical.region.kind != OSPREY_REGION_HEAP_SITE) {
        return o->prov_object_id == 0 && o->prov_generation == 0;
    }
    if (o->prov_object_id == 0) {
        return false;
    }
    ProvenanceObject *obj =
        provenance_lookup_object(o->prov_object_id, o->prov_generation);
    if (obj == NULL || obj->state != PROV_OBJ_LIVE) {
        return false;
    }
    if (o->concrete_value < obj->base) {
        return false;
    }
    uint64_t delta = (uint64_t)(o->concrete_value - obj->base);
    if (delta > obj->requested_size || delta > INT64_MAX ||
        o->canonical.offset != (int64_t)delta) {
        return false;
    }
    uint64_t site = 0;
    if (!osprey_normalize_pc(obj->alloc_pc, &site) ||
        o->canonical.region.kind != OSPREY_REGION_HEAP_SITE ||
        o->canonical.region.site_offset != site) {
        return false;
    }
    return true;
}

/* Provenance-authoritative heap origin check (public; F02 selection and
 * reload use it). */
bool osprey_address_origin_live(const OspreyAddressOrigin *o) {
    if (o == NULL || !o->valid || o->width != sizeof(target_ulong)) {
        return false;
    }
    return origin_heap_prov_ok(o);
}

/* Exact sparse overlap invalidation: remove every live memory-shadow
 * slot overlapping [addr, addr+size).  A slot occupies
 * [slot_addr, slot_addr + OSPREY_SHADOW_ALIGN); the write occupies
 * [addr, addr + size).  Iterates the live slots only, never every
 * 8-byte slot in the interval.  Zero-size writes are no-ops.  A
 * wrapping write interval clears the entire shadow: the only safe
 * response when exact overlap cannot be represented. */
static void origin_invalidate_mem_range(OspreyCpuOriginState *st,
                                        target_ulong addr,
                                        target_ulong size) {
    if (st->mem_slots == NULL || size == 0) {
        return;
    }
    target_ulong last = addr + (size - 1);
    if (last < addr) {
        /* Wrapping interval: clear the whole shadow. */
        g_hash_table_remove_all(st->mem_slots);
        return;
    }
    GHashTableIter it;
    gpointer key, value;
    g_hash_table_iter_init(&it, st->mem_slots);
    while (g_hash_table_iter_next(&it, &key, &value)) {
        target_ulong slot = (target_ulong)GPOINTER_TO_SIZE(key);
        /* Overlap: slot start at or before the inclusive write end AND
         * write start strictly before the slot end
         * [slot, slot + OSPREY_SHADOW_ALIGN).  slot is aligned so
         * slot + ALIGN wraps only for the single top-of-space slot,
         * whose span reaches 2^64 (treated as covering any write whose
         * end is at or past the slot start). */
        if (slot <= last) {
            target_ulong slot_end = slot + OSPREY_SHADOW_ALIGN;
            if (addr < slot_end || slot_end < slot) {
                g_hash_table_iter_remove(&it);
            }
        }
    }
}

/* Install one aligned pointer-width memory-shadow slot from a live,
 * value-matching ADDRESS origin.  Stage 2.4: every successful store
 * path invalidates overlap FIRST via origin_invalidate_mem_range();
 * this function only installs the exact replacement after
 * invalidation.  Callers with no eligible source call only the
 * invalidation. */
static void origin_install_mem_slot(CPUArchState *env, target_ulong addr,
                                    const OspreyAddressOrigin *src) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    if (st->mem_slots == NULL) return;
    if (src == NULL || !src->valid) {
        return; /* no replacement; invalidation already ran */
    }
    OspreyMemAddressOrigin *slot = g_new0(OspreyMemAddressOrigin, 1);
    slot->valid = 1;
    slot->width = src->width;
    slot->canonical = src->canonical;
    slot->concrete_value = src->concrete_value;
    slot->prov_object_id = src->prov_object_id;
    slot->prov_generation = src->prov_generation;
    g_hash_table_replace(st->mem_slots, GSIZE_TO_POINTER(addr), slot);
}

/* Exact aligned pointer-width reload: restore an ADDRESS origin into
 * dst_reg only when the slot is valid, its saved concrete value equals
 * the observed runtime value, and (for heap origins) the provenance
 * identity is still live.  Any failure removes the exact slot.  The
 * function replaces the destination ADDRESS channel on every
 * pointer-width load and never wipes the VALUE channel (the two channels
 * are independent).  producer_pc is the normalized load
 * instruction. */
static void origin_load_slot(CPUArchState *env, target_ulong addr,
                             int dst_reg, target_ulong value,
                             uint64_t producer_pc) {
    if (dst_reg < 0 || dst_reg >= CPU_NB_REGS) {
        return;
    }
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    /* A pointer-width load defines the destination ADDRESS channel.
     * Clear any pre-load origin before consulting the shadow: an
     * untagged cell containing the same numeric pointer is not evidence
     * that the loaded value retained the old identity.  VALUE remains
     * independent and is installed by osprey_on_mem_load(). */
    memset(&st->regs[dst_reg].address, 0,
           sizeof(st->regs[dst_reg].address));
    if (st->mem_slots == NULL) {
        return;
    }
    OspreyMemAddressOrigin *slot = g_hash_table_lookup(
        st->mem_slots, GSIZE_TO_POINTER(addr));
    if (slot == NULL || !slot->valid) {
        return;
    }
    if (slot->width != sizeof(target_ulong) ||
        slot->concrete_value != value) {
        /* Value-consistency/width failure: the slot's bytes no longer
         * match the saved tag.  Remove the stale entry so a later
         * coincidental byte match cannot resurrect it. */
        g_hash_table_remove(st->mem_slots, GSIZE_TO_POINTER(addr));
        return;
    }
    if (slot->prov_object_id != 0) {
        OspreyAddressOrigin tmp;
        memset(&tmp, 0, sizeof(tmp));
        tmp.valid = 1;
        tmp.width = slot->width;
        tmp.concrete_value = slot->concrete_value;
        tmp.canonical = slot->canonical;
        tmp.prov_object_id = slot->prov_object_id;
        tmp.prov_generation = slot->prov_generation;
        if (!origin_heap_prov_ok(&tmp)) {
            g_hash_table_remove(st->mem_slots, GSIZE_TO_POINTER(addr));
            return;
        }
    }
    OspreyAddressOrigin *o = &st->regs[dst_reg].address;
    memset(o, 0, sizeof(*o));
    o->valid = 1;
    o->width = (uint8_t)sizeof(target_ulong);
    o->concrete_value = value;
    o->canonical = slot->canonical;
    o->prov_object_id = slot->prov_object_id;
    o->prov_generation = slot->prov_generation;
    o->producer_pc = producer_pc;
}

/* Full-width register copy: transfer the ADDRESS and VALUE channels
 * independently with value-consistency checks, replacing the ADDRESS
 * producer PC with the MOV instruction.  Each channel survives only
 * when its concrete value matches the corresponding post-MOV register
 * value (self-MOV preserves both channels once).  The two channels are
 * independent: a MOV of a register that carries only a VALUE origin
 * preserves that VALUE, and vice versa.  RSP lifecycle seeds
 * (osprey_on_rsp_update) remain authoritative: an unknown full-width
 * MOV to RSP preserves the just-derived stack identity while clearing
 * only the VALUE channel. */
static void origin_mov_reg(CPUArchState *env, int dst, int src,
                           target_ulong src_val, target_ulong dst_val,
                           uint64_t producer_pc) {
    if (dst < 0 || dst >= CPU_NB_REGS) {
        return;
    }
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    if (src < 0 || src >= CPU_NB_REGS) {
        origin_invalidate_reg(env, dst);
        return;
    }
    /* Snapshot the complete source channels before clearing the
     * destination: dst == src is a valid self-MOV. */
    OspreyAddressOrigin source = st->regs[src].address;
    OspreyValueOrigin source_v = st->regs[src].value;

    /* ADDRESS channel: valid, pointer-width, value-matching, and live
     * sources transfer with the MOV producer PC.  The RSP lifecycle
     * exception preserves a just-derived stack identity when the
     * source is unknown. */
    bool addr_ok = source.valid && source.width == sizeof(target_ulong) &&
        source.concrete_value == src_val && src_val == dst_val &&
        osprey_address_origin_live(&source);
    if (addr_ok) {
        origin_install_address(env, dst, &source.canonical,
                               source.prov_object_id,
                               source.prov_generation, producer_pc,
                               dst_val);
    } else if (dst == R_ESP &&
               st->regs[dst].address.valid &&
               st->regs[dst].address.width == sizeof(target_ulong) &&
               st->regs[dst].address.concrete_value == dst_val &&
               st->regs[dst].address.canonical.region.kind ==
                   OSPREY_REGION_STACK_FUNCTION) {
        /* A full-width MOV to RSP with an unknown source: preserve the
         * immediately preceding osprey_on_rsp_update() result (a stack
         * identity independently re-derived from the live frame and
         * concrete RSP) instead of erasing it. */
    } else {
        memset(&st->regs[dst].address, 0, sizeof(st->regs[dst].address));
    }

    /* VALUE channel: independent preservation when the concrete value
     * survives the copy. */
    if (source_v.valid && source_v.concrete_value == dst_val) {
        st->regs[dst].value = source_v;
    } else {
        memset(&st->regs[dst].value, 0, sizeof(st->regs[dst].value));
    }
}

/* lea dst, [base + disp]: propagate the ADDRESS origin with
 * offset += disp when the runtime reconstruction is exact
 * (base + disp == dst modulo target width) and the checked signed
 * canonical-offset addition succeeds.  Preserves heap provenance
 * identity. */
static void origin_lea_imm(CPUArchState *env, int dst, int base,
                           int64_t disp, target_ulong dst_val,
                           target_ulong base_val, uint64_t producer_pc) {
    if (dst < 0 || dst >= CPU_NB_REGS) {
        return;
    }
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    if (base < 0 || base >= CPU_NB_REGS) {
        origin_invalidate_reg(env, dst);
        return;
    }
    /* Preserve the source across an in-place LEA (dst == base). */
    OspreyAddressOrigin source = st->regs[base].address;
    if (!source.valid || source.width != sizeof(target_ulong) ||
        source.concrete_value != base_val) {
        origin_invalidate_reg(env, dst);
        return;
    }
    /* x86 address arithmetic wraps mod 2^64: exact wrapping
     * reconstruction is required before the tracked-offset fold. */
    target_ulong expect = base_val + (target_ulong)disp;
    if (expect != dst_val) {
        origin_invalidate_reg(env, dst);
        return;
    }
    if (!osprey_address_origin_live(&source)) {
        origin_invalidate_reg(env, dst);
        return;
    }
    int64_t off = 0;
    if (!osprey_check_add(source.canonical.offset, disp, &off)) {
        origin_invalidate_reg(env, dst);
        return;
    }
    OspreyAddress canonical = source.canonical;
    canonical.offset = off;
    origin_install_address(env, dst, &canonical, source.prov_object_id,
                           source.prov_generation, producer_pc, dst_val);
}

/* ADD/SUB immediate: fold `delta` into the tagged register's canonical
 * offset after exact wrapping reconstruction. */
static void origin_addsub_imm(CPUArchState *env, int reg, int64_t delta,
                              target_ulong pre_val, target_ulong post_val,
                              uint64_t producer_pc) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    if (reg < 0 || reg >= CPU_NB_REGS) return;
    OspreyAddressOrigin *o = &st->regs[reg].address;
    target_ulong expect = pre_val + (target_ulong)delta;
    if (expect != post_val) {
        origin_invalidate_reg(env, reg);
        return;
    }
    /* gen_op_mov_reg_v publishes the architectural RSP lifecycle update
     * before this arithmetic helper.  When that exact stack seed is
     * already present, it is authoritative for the post-write value and
     * must not be rejected for failing the pre-value comparison below. */
    if (reg == R_ESP && o->valid &&
        o->width == sizeof(target_ulong) &&
        o->concrete_value == post_val &&
        o->canonical.region.kind == OSPREY_REGION_STACK_FUNCTION &&
        o->producer_pc == producer_pc && osprey_address_origin_live(o)) {
        memset(&st->regs[reg].value, 0, sizeof(st->regs[reg].value));
        return;
    }
    if (!o->valid || o->width != sizeof(target_ulong) ||
        o->concrete_value != pre_val) {
        origin_invalidate_reg(env, reg);
        return;
    }
    if (!osprey_address_origin_live(o)) {
        origin_invalidate_reg(env, reg);
        return;
    }
    int64_t off = 0;
    if (!osprey_check_add(o->canonical.offset, delta, &off)) {
        origin_invalidate_reg(env, reg);
        return;
    }
    OspreyAddress canonical = o->canonical;
    canonical.offset = off;
    origin_install_address(env, reg, &canonical, o->prov_object_id,
                           o->prov_generation, producer_pc, post_val);
}

/* ADD/SUB register: accept exactly the one-origin forms — tagged
 * destination plus untagged source for ADD or SUB, and untagged
 * destination plus tagged source for ADD.  The untagged operand is
 * derived from the observed post-result/source values; the signed
 * operand is checked-folded into the tagged canonical offset.  Never
 * negate INT64_MIN (SUB folds through osprey_check_sub). */
static void origin_addsub_reg(CPUArchState *env, int dst, int src,
                              bool is_sub, target_ulong dst_val,
                              target_ulong src_val,
                              uint64_t producer_pc) {
    if (dst < 0 || dst >= CPU_NB_REGS) {
        return;
    }
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    if (src < 0 || src >= CPU_NB_REGS) {
        origin_invalidate_reg(env, dst);
        return;
    }
    OspreyAddressOrigin *d = &st->regs[dst].address;
    OspreyAddressOrigin *s = &st->regs[src].address;
    if ((d->valid && d->width != sizeof(target_ulong)) ||
        (s->valid && s->width != sizeof(target_ulong))) {
        origin_invalidate_reg(env, dst);
        return;
    }
    bool d_tagged = d->valid;
    bool s_tagged = s->valid;

    OspreyAddressOrigin *tagged = NULL;
    if (d_tagged && !s_tagged) {
        /* Tagged destination plus untagged source for ADD or SUB.  The
         * origin channel still holds the PRE-instruction concrete value
         * (write-back invalidation was suppressed); exact wrapping
         * reconstruction requires pre ± src == post (mod target width),
         * then the signed operand is checked-folded into the canonical
         * offset (ADD via check_add, SUB via check_sub — the source
         * value is never negated, so INT64_MIN cannot wrap). */
        tagged = d;
        if (!tagged->valid || tagged->width != sizeof(target_ulong)) {
            origin_invalidate_reg(env, dst);
            return;
        }
        target_ulong expect = is_sub
            ? tagged->concrete_value - (target_ulong)src_val
            : tagged->concrete_value + (target_ulong)src_val;
        if (expect != dst_val) {
            origin_invalidate_reg(env, dst);
            return;
        }
        if (!osprey_address_origin_live(tagged)) {
            origin_invalidate_reg(env, dst);
            return;
        }
        int64_t off = 0;
        bool ok = is_sub
            ? osprey_check_sub(tagged->canonical.offset,
                               (int64_t)src_val, &off)
            : osprey_check_add(tagged->canonical.offset,
                               (int64_t)src_val, &off);
        if (!ok) {
            origin_invalidate_reg(env, dst);
            return;
        }
        OspreyAddress canonical = tagged->canonical;
        canonical.offset = off;
        origin_install_address(env, dst, &canonical, tagged->prov_object_id,
                               tagged->prov_generation, producer_pc,
                               dst_val);
        return;
    }
    if (!d_tagged && s_tagged && !is_sub) {
        /* Untagged destination plus tagged source for ADD: the tagged
         * source is the base; the untagged operand is the observed
         * post-result minus the source value (wrapping), folded into
         * the tagged canonical offset with checked addition. */
        if (!s->valid || s->width != sizeof(target_ulong) ||
            s->concrete_value != src_val) {
            origin_invalidate_reg(env, dst);
            return;
        }
        if (!osprey_address_origin_live(s)) {
            origin_invalidate_reg(env, dst);
            return;
        }
        int64_t delta = (int64_t)(dst_val - src_val);
        OspreyAddress canonical = s->canonical;
        int64_t off = 0;
        if (!osprey_check_add(canonical.offset, delta, &off)) {
            origin_invalidate_reg(env, dst);
            return;
        }
        canonical.offset = off;
        origin_install_address(env, dst, &canonical, s->prov_object_id,
                               s->prov_generation, producer_pc, dst_val);
        return;
    }
    /* Two tagged operands, SUB with only the source tagged, or no
     * eligible tagged operand: no sound merge. */
    origin_invalidate_reg(env, dst);
}

/* Full-width register XCHG: swap the two pre-exchange ADDRESS and
 * VALUE channels independently, validating each channel against the
 * corresponding post-swap concrete value.  Each surviving side
 * receives the XCHG producer PC; an invalid side stays invalid.
 * dst == src validates and refreshes the single channels once. */
static void origin_xchg_reg(CPUArchState *env, int dst, int src,
                            target_ulong dst_val, target_ulong src_val,
                            uint64_t producer_pc) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    if (dst < 0 || dst >= CPU_NB_REGS) return;
    if (dst == src) {
        /* Self-XCHG is an identity operation.  Validate ADDRESS and
         * VALUE independently: absence or failure in one channel must
         * not erase sound metadata in the other. */
        OspreyAddressOrigin *o = &st->regs[dst].address;
        if (o->valid) {
            if (o->width == sizeof(target_ulong) &&
                o->concrete_value == dst_val &&
                osprey_address_origin_live(o)) {
                o->producer_pc = producer_pc;
            } else {
                memset(o, 0, sizeof(*o));
            }
        }
        OspreyValueOrigin *v = &st->regs[dst].value;
        if (v->valid && v->concrete_value != dst_val) {
            memset(v, 0, sizeof(*v));
        }
        return;
    }
    if (src < 0 || src >= CPU_NB_REGS) {
        origin_invalidate_reg(env, dst);
        return;
    }
    OspreyAddressOrigin da = st->regs[dst].address;
    OspreyAddressOrigin sa = st->regs[src].address;
    OspreyAddressOrigin new_d, new_s;
    memset(&new_d, 0, sizeof(new_d));
    memset(&new_s, 0, sizeof(new_s));
    /* Post-swap, dst holds the pre-exchange src value (dst_val) and src
     * holds the pre-exchange dst value (src_val).  The channel that
     * lands in each register is the OTHER register's pre-exchange
     * channel, validated independently against the post-swap concrete
     * value; an invalid side stays invalid. */
    bool d_ok = sa.valid && sa.width == sizeof(target_ulong) &&
        sa.concrete_value == dst_val && osprey_address_origin_live(&sa);
    bool s_ok = da.valid && da.width == sizeof(target_ulong) &&
        da.concrete_value == src_val && osprey_address_origin_live(&da);
    if (d_ok) {
        new_d = sa;
        new_d.concrete_value = dst_val;
        new_d.producer_pc = producer_pc;
    }
    if (s_ok) {
        new_s = da;
        new_s.concrete_value = src_val;
        new_s.producer_pc = producer_pc;
    }
    st->regs[dst].address = new_d;
    st->regs[src].address = new_s;
    /* VALUE channels swap under the same post-swap value validation:
     * the channel landing in dst must match dst_val, and the channel
     * landing in src must match src_val. */
    OspreyValueOrigin dv = st->regs[dst].value;
    OspreyValueOrigin sv = st->regs[src].value;
    memset(&st->regs[dst].value, 0, sizeof(st->regs[dst].value));
    memset(&st->regs[src].value, 0, sizeof(st->regs[src].value));
    if (sv.valid && sv.concrete_value == dst_val) {
        st->regs[dst].value = sv;
    }
    if (dv.valid && dv.concrete_value == src_val) {
        st->regs[src].value = dv;
    }
}

/* Normalize a raw producer PC to its image-relative offset.  Returns
 * false when the PC is outside the main image: the transfer must then
 * kill the destination rather than install an origin. */
static bool origin_normalize_producer(target_ulong raw_pc,
                                      uint64_t *norm_pc) {
    return osprey_normalize_pc(raw_pc, norm_pc);
}

/* Runtime helpers exposed to the translator wrappers. */
void osprey_on_reg_materialize_address(CPUArchState *env, uint32_t dst,
                                       target_ulong value,
                                       target_ulong pc) {
    uint64_t norm_pc = 0;
    if (!origin_normalize_producer(pc, &norm_pc)) {
        origin_invalidate_reg(env, (int)dst);
        return;
    }
    /* Full-width result is guaranteed by the translator callsite; only
     * a main-image global address may seed an origin.  Never seed heap,
     * stack, anonymous-map, library, or merely mapped numeric values
     * from an immediate. */
    OspreyRegionId region;
    int64_t off = 0;
    if (!osprey_region_of_addr(env, value, &region, &off, false) ||
        region.kind != OSPREY_REGION_GLOBAL) {
        origin_invalidate_reg(env, (int)dst);
        return;
    }
    OspreyAddress canonical;
    canonical.region = region;
    canonical.offset = off;
    origin_install_address(env, (int)dst, &canonical, 0, 0, norm_pc,
                           value);
}

void osprey_on_reg_copy(CPUArchState *env, uint32_t dst, uint32_t src,
                        target_ulong src_value, target_ulong dst_value,
                        target_ulong pc) {
    uint64_t norm_pc = 0;
    if (!origin_normalize_producer(pc, &norm_pc)) {
        origin_invalidate_reg(env, (int)dst);
        return;
    }
    origin_mov_reg(env, (int)dst, (int)src, src_value, dst_value, norm_pc);
}

void osprey_on_reg_lea(CPUArchState *env, uint32_t dst, uint32_t base,
                       int64_t disp, target_ulong dst_value,
                       target_ulong base_value, target_ulong pc) {
    uint64_t norm_pc = 0;
    if (!origin_normalize_producer(pc, &norm_pc)) {
        origin_invalidate_reg(env, (int)dst);
        return;
    }
    origin_lea_imm(env, (int)dst, (int)base, disp, dst_value, base_value,
                   norm_pc);
}

void osprey_on_reg_addsub_imm(CPUArchState *env, uint32_t reg,
                              int64_t delta, target_ulong pre_value,
                              target_ulong post_value, target_ulong pc) {
    uint64_t norm_pc = 0;
    if (!origin_normalize_producer(pc, &norm_pc)) {
        origin_invalidate_reg(env, (int)reg);
        return;
    }
    origin_addsub_imm(env, (int)reg, delta, pre_value, post_value, norm_pc);
}

void osprey_on_reg_addsub_reg(CPUArchState *env, uint32_t dst,
                              uint32_t src, bool is_sub,
                              target_ulong dst_value,
                              target_ulong src_value, target_ulong pc) {
    uint64_t norm_pc = 0;
    if (!origin_normalize_producer(pc, &norm_pc)) {
        origin_invalidate_reg(env, (int)dst);
        return;
    }
    origin_addsub_reg(env, (int)dst, (int)src, is_sub, dst_value,
                      src_value, norm_pc);
}

void osprey_on_reg_xchg(CPUArchState *env, uint32_t dst, uint32_t src,
                        target_ulong dst_value, target_ulong src_value,
                        target_ulong pc) {
    uint64_t norm_pc = 0;
    if (!origin_normalize_producer(pc, &norm_pc)) {
        origin_invalidate_reg(env, (int)dst);
        origin_invalidate_reg(env, (int)src);
        return;
    }
    origin_xchg_reg(env, (int)dst, (int)src, dst_value, src_value,
                    norm_pc);
}

void osprey_on_reg_invalidate(CPUArchState *env, uint32_t reg) {
    origin_invalidate_reg(env, (int)reg);
}

/* Combined Stage 2.4 load hook.  Runs only after a successful guest
 * load into a named GPR; the helper passed the post-load architectural
 * value from env->regs[dst].  Constructs the VALUE and ADDRESS channels
 * independently:
 *  - VALUE: a load into a named GPR is always a new value; for widths
 *    1/2/4/8 the source interval must resolve as one exact canonical
 *    chunk and the complete post-load GPR value is recorded with the
 *    source width.  Main-image loads only (the F01 producer gate).
 *  - ADDRESS: an aligned pointer-width load restores the exact shadow
 *    slot only when width, saved pointer value, and heap liveness
 *    match; the normalized load PC becomes the new producer.
 *    Non-pointer-width loads leave the existing channel untouched: a
 *    stale tag stays inert because every consumer re-checks the
 *    concrete value, and Stage 2.3 F02 continuity rows depend on the
 *    base origin surviving byte loads (glibc-startup scans).
 * A missing/stale ADDRESS slot never erases a valid new VALUE origin;
 * a source outside modeled regions may still restore a valid ADDRESS
 * shadow but cannot create a VALUE origin. */
void osprey_on_mem_load(CPUArchState *env, uint32_t dst,
                        target_ulong addr, target_ulong size,
                        uint64_t pc) {
    if (dst >= CPU_NB_REGS) {
        return;
    }
    uint64_t norm_pc = 0;
    bool pc_ok = origin_normalize_producer((target_ulong)pc, &norm_pc);
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    bool is_ptr_load = (size == OSPREY_SHADOW_ALIGN &&
                        (addr & (OSPREY_SHADOW_ALIGN - 1)) == 0);

    /* VALUE channel: a load into a named GPR is always a new value.
     * Only a canonical source chunk can back F03, and F03 is
     * main-image evidence: the load instruction must be inside the
     * main image (the F01 producer gate).  Out-of-image loads (libc
     * internals) never create VALUE origins. */
    memset(&st->regs[dst].value, 0, sizeof(st->regs[dst].value));
    if (pc_ok && (size == 1 || size == 2 || size == 4 || size == 8)) {
        OspreyChunk src_chunk;
        if (osprey_chunk_of_interval(env, addr, (target_ulong)size,
                                     &src_chunk)) {
            OspreyValueOrigin *v = &st->regs[dst].value;
            v->valid = 1;
            v->width = (uint8_t)size;
            v->concrete_value = env->regs[dst];
            v->source = src_chunk;
        }
    }

    /* ADDRESS channel: only an aligned pointer-width reload from the
     * shadow may replace it; origin_load_slot clears the register on
     * any failure.  Non-pointer-width loads (byte/word/dword) leave
     * the existing channel untouched: a stale tag stays inert because
     * every consumer re-checks the concrete value, and Stage 2.3 F02
     * continuity rows (t02's loop reloads) depend on the base origin
     * surviving.  The shadow may legitimately cover storage outside
     * modeled regions (sound spill/reload), so no canonical resolution
     * is required here.
     *
     * The value-consistency check re-reads the guest memory instead of
     * trusting env->regs[dst]: helpers can observe a stale register
     * (the architectural load may not have reached the register when
     * the helper runs), and a wrong value would remove a live slot via
     * the mismatch path (t02 regression).  The VALUE channel above
     * keeps the post-load GPR value per the Stage 2.4 contract. */
    if (is_ptr_load) {
        if (pc_ok) {
            target_ulong mem_value = env->regs[dst];
            if (is_valid_address(addr, false)) {
                memcpy(&mem_value, g2h(addr), sizeof(mem_value));
            }
            origin_load_slot(env, addr, (int)dst, mem_value, norm_pc);
        } else {
            /* Out-of-image pointer reload: Stage 2.3 semantics, the
             * register channels are invalidated. */
            memset(&st->regs[dst], 0, sizeof(st->regs[dst]));
        }
    }
}

/* Combined Stage 2.4 store hook.  Runs only after a successful guest
 * store.  The raw instruction PC rides the pending transfer-PC scratch
 * (consumed by helper_sem_on_store).  F03/F04 publication is
 * main-image evidence: an out-of-image store (libc internals spilling
 * register channels into their own state) still invalidates overlap
 * and may install/replace shadow slots (Stage 2.3 behavior) but
 * publishes no facts.  Otherwise: snapshots the source register
 * channels, invalidates all destination overlap, then evaluates F03,
 * F04, and ADDRESS slot installation independently:
 *  - F03 MemCopy(source,destination): source VALUE channel valid,
 *    value.width == store size (1/2/4/8), concrete value matches, and
 *    the destination interval resolves as one exact canonical chunk.
 *    Alignment is irrelevant to the logical F03 fact.
 *  - F04 PointsTo(pointer_chunk,target): store size is exactly
 *    pointer-width, the source ADDRESS channel is valid,
 *    pointer-width, value-matching, and live, and the destination
 *    pointer cell resolves as one exact canonical chunk.
 *  - Slot installation: only when the store is exactly pointer-width
 *    AND destination-aligned AND the source ADDRESS origin is live and
 *    value-matching.  F04 publication does not require alignment;
 *    alignment limits shadow installation only.
 * A register may satisfy both channels; failure of one channel never
 * suppresses the other. */
void osprey_on_mem_store(CPUArchState *env, uint32_t src,
                         target_ulong addr, target_ulong size,
                         target_ulong src_value, target_ulong pc) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    /* F03/F04 are main-image evidence: the storing instruction must be
     * inside the main image (the same producer gate F01/F02 use).
     * Out-of-image stores (libc internals spilling registers into
     * their own state, signal frames, etc.) must still invalidate
     * overlap and may replace a sound slot, but never publish facts. */
    uint64_t norm_pc = 0;
    bool pc_ok = origin_normalize_producer(pc, &norm_pc);
    (void)norm_pc; /* publication gate only; slot install is not gated */
    OspreyAddressOrigin src_addr;
    OspreyValueOrigin src_value_origin;
    memset(&src_addr, 0, sizeof(src_addr));
    memset(&src_value_origin, 0, sizeof(src_value_origin));
    bool have_addr = false, have_value = false;
    if (src < CPU_NB_REGS) {
        src_addr = st->regs[src].address;
        src_value_origin = st->regs[src].value;
        have_addr = src_addr.valid;
        have_value = src_value_origin.valid;
    }
    /* Invalidate first: every overlapping slot is removed before any
     * exact replacement is considered. */
    origin_invalidate_mem_range(st, addr, size);
    if (st->mem_slots == NULL) {
        return; /* no shadow installed: nothing further to mutate */
    }

    OspreySharedRun *run = g_shared_run;

    /* F03: data-flow evidence from a live VALUE channel.  The saved
     * source chunk must be a real modeled chunk: a nonempty source with
     * a modeled region kind.  A zero-initialized (never-loaded) source
     * publishes nothing — the VALUE channel must have been created by
     * a concrete successful load.  F03 is main-image evidence: the
     * storing instruction must be inside the main image (the same
     * producer gate F01/F02 use); out-of-image stores (libc internals
     * spilling registers into their own state) only invalidate. */
    if (pc_ok && have_value && run != NULL &&
        (size == 1 || size == 2 || size == 4 || size == 8) &&
        src_value_origin.width == (uint8_t)size &&
        src_value_origin.source.size == size &&
        src_value_origin.concrete_value == src_value &&
        (src_value_origin.source.address.region.kind ==
             OSPREY_REGION_GLOBAL ||
         src_value_origin.source.address.region.kind ==
             OSPREY_REGION_HEAP_SITE ||
         src_value_origin.source.address.region.kind ==
             OSPREY_REGION_STACK_FUNCTION)) {
        OspreyChunk dst_chunk;
        if (osprey_chunk_of_interval(env, addr, (target_ulong)size,
                                     &dst_chunk)) {
            OspreyCopyFact fact;
            memset(&fact, 0, sizeof(fact));
            fact.source = src_value_origin.source;
            fact.destination = dst_chunk;
            fact.sample_support = 1;
            qemu_mutex_lock(&g_shared_mutex);
            osprey_table_insert_copy(run, &fact);
            qemu_mutex_unlock(&g_shared_mutex);
        }
    }

    /* F04: address-origin evidence for an exact pointer-width store.
     * The destination pointer cell must be canonical; alignment only
     * limits shadow installation below, not the fact itself.  F04 is
     * main-image evidence, same gate as F03. */
    if (pc_ok && have_addr && run != NULL &&
        size == (target_ulong)sizeof(target_ulong) &&
        src_addr.width == sizeof(target_ulong) &&
        src_addr.concrete_value == src_value &&
        osprey_address_origin_live(&src_addr)) {
        OspreyChunk cell;
        if (osprey_chunk_of_interval(env, addr, sizeof(target_ulong),
                                     &cell)) {
            OspreyPointsToFact fact;
            memset(&fact, 0, sizeof(fact));
            fact.pointer_chunk = cell;
            fact.target = src_addr.canonical;
            fact.sample_support = 1;
            fact.weak_numeric_evidence = 0;
            qemu_mutex_lock(&g_shared_mutex);
            osprey_table_insert_points(run, &fact);
            qemu_mutex_unlock(&g_shared_mutex);
        }
    }

    /* Aligned pointer-width replacement slot: only when the store is
     * exactly pointer-width, destination-aligned, and the source
     * ADDRESS origin is live and value-matching.  Installation is
     * allowed even when the pointer cell lies outside a modeled
     * region (sound spill/reload); F04 still required the canonical
     * cell above. */
    if (have_addr &&
        size == (target_ulong)sizeof(target_ulong) &&
        (addr & (OSPREY_SHADOW_ALIGN - 1)) == 0 &&
        src_addr.width == sizeof(target_ulong) &&
        src_addr.concrete_value == src_value &&
        osprey_address_origin_live(&src_addr)) {
        origin_install_mem_slot(env, addr, &src_addr);
    }
}

/* External/unknown-source overwrite: exact overlap invalidation only.
 * No fact, no replacement metadata.  Zero-size writes are no-ops. */
void osprey_on_mem_overwrite(CPUArchState *env, target_ulong addr,
                             target_ulong size) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    origin_invalidate_mem_range(st, addr, size);
}

/* ------------------------------------------------------------------ */
/* Allocation instance tracking                                        */
/* ------------------------------------------------------------------ */

static void osprey_ensure_mutex(void) {
    if (!g_shared_mutex_init) {
        qemu_mutex_init(&g_shared_mutex);
        g_shared_mutex_init = true;
    }
}

void osprey_free_runtime_regions(void) {
    if (g_stack_frames != NULL) {
        g_array_free(g_stack_frames, TRUE);
        g_stack_frames = NULL;
    }
    if (g_heap_instances != NULL) {
        g_array_free(g_heap_instances, TRUE);
        g_heap_instances = NULL;
    }
    g_next_stack_instance = 1;
    g_next_heap_instance = 1;
    g_shared_run = NULL;
}

/* Re-record the live runtime region catalog into a freshly reset
 * shared run: frames/heaps that predate the per-sample reset (e.g. the
 * entrypoint's own frame) never re-fire their hooks, so the parent
 * would otherwise lack their instances when mapping raw addresses. */
static void osprey_backfill_instances(void) {
    OspreySharedRun *run = g_shared_run;
    if (run == NULL) return;
    if (g_stack_frames != NULL) {
        for (guint i = 0; i < g_stack_frames->len; i++) {
            const OspreyStackFrame *f = &g_array_index(
                g_stack_frames, OspreyStackFrame, i);
            if (f->region.site_offset == OSPREY_STACK_IMPRECISE_SITE) {
                continue; /* imprecise frames never contribute facts */
            }
            record_region_instance(&f->region, f->instance_id, f->entry_sp,
                                   f->min_sp, f->max_sp, 0, 0);
        }
    }
    if (g_heap_instances != NULL) {
        for (guint i = 0; i < g_heap_instances->len; i++) {
            const HeapInstance *h = &g_array_index(
                g_heap_instances, HeapInstance, i);
            if (h->live) {
                uint64_t raw_base = (uint64_t)h->base;
                if (raw_base > UINT64_MAX - h->size) {
                    run->bad_arithmetic = 1;
                    return;
                }
                record_region_instance(&h->region, h->instance_id,
                                       h->base, raw_base,
                                       raw_base + h->size,
                                       h->prov_object_id,
                                       h->prov_generation);
            }
        }
    }
    /* Global region: ONE merged instance per sample with the union
     * span, raw_base = image base so raw_base + image-relative offset
     * maps back to the runtime address. */
    OspreyContext *ctx = osprey_ctx_ref();
    if (ctx != NULL && ctx->global_ranges != NULL &&
        ctx->global_ranges->len > 0) {
        int64_t hi = 0;
        for (guint i = 0; i < ctx->global_ranges->len; i++) {
            const OspreyGlobalRange *e = &g_array_index(
                ctx->global_ranges, OspreyGlobalRange, i);
            if (e->extent > INT64_MAX || e->offset < 0 ||
                e->offset > INT64_MAX - (int64_t)e->extent) {
                run->bad_arithmetic = 1;
                return;
            }
            int64_t end = e->offset + (int64_t)e->extent;
            if (end > hi) {
                hi = end;
            }
        }
        if (hi > 0) {
            uint64_t image_base = (uint64_t)osprey_get_image_base();
            if (image_base > UINT64_MAX - (uint64_t)hi) {
                run->bad_arithmetic = 1;
                return;
            }
            OspreyRegionId gid;
            gid.kind = OSPREY_REGION_GLOBAL;
            gid.code_image_id = 0;
            gid.site_offset = 0;
            record_region_instance(&gid, 0, (target_ulong)image_base,
                                   image_base, image_base + (uint64_t)hi,
                                   0, 0);
        }
    }
}

void osprey_child_use_shared_run(OspreyContext *ctx, OspreySharedRun *run) {
    if (ctx == NULL || run == NULL) return;
    osprey_ensure_mutex();
    g_shared_run = run;
    osprey_backfill_instances();
}

/* Mark the current sample as unsupported (multithreaded guest via
 * CLONE_VM).  The parent rejects the merge; no facts are trusted. */
void osprey_mark_unsupported_execution(void) {
    OspreySharedRun *run = g_shared_run;
    if (run != NULL) {
        run->unsupported_execution = 1;
    }
    /* do_fork marks this while the new host thread is still blocked on
     * clone_lock, after the parallel-execution TB flush.  Disable new
     * OSPREY instrumentation before either guest thread resumes. */
    osprey_collect_enabled = 0;
}

/* Record one live canonical region instance into the shared run
 * (parent needs the raw base to map mutation addresses). */
static void record_region_instance(const OspreyRegionId *region,
                                   uint64_t instance_id,
                                   target_ulong raw_base,
                                   uint64_t raw_min,
                                   uint64_t raw_max,
                                   uint64_t prov_object_id,
                                   uint32_t prov_generation) {
    OspreySharedRun *run = g_shared_run;
    if (run == NULL) return;
    OspreyRegionInstance f;
    memset(&f, 0, sizeof(f));
    f.region = *region;
    f.instance_id = instance_id;
    f.raw_base = (uint64_t)raw_base;
    f.raw_min = raw_min;
    f.raw_max = raw_max;
    f.prov_object_id = prov_object_id;
    f.prov_generation = prov_generation;
    f.sample_support = 1;
    qemu_mutex_lock(&g_shared_mutex);
    osprey_table_insert_region(run, &f);
    qemu_mutex_unlock(&g_shared_mutex);
}

void osprey_on_alloc_success(CPUArchState *env,
                             const OspreyAllocatorObservation *obs,
                             target_ulong base,
                             uint64_t object_id, uint32_t generation) {
    if (obs == NULL) {
        if (g_shared_run != NULL) {
            g_shared_run->bad_identity = 1;
        }
        return;
    }
    if (obs->kind != OSPREY_ALLOCATOR_MALLOC &&
        obs->kind != OSPREY_ALLOCATOR_CALLOC &&
        obs->kind != OSPREY_ALLOCATOR_REALLOC) {
        if (g_shared_run != NULL) {
            g_shared_run->bad_identity = 1;
        }
        return;
    }
    uint64_t norm_pc = 0;
    if (!osprey_normalize_pc(obs->site_pc, &norm_pc)) {
        /* Allocation from out-of-image code (libc-internal): the site
         * is not part of the main image; record nothing. */
        return;
    }
    uint64_t raw_base = (uint64_t)base;
    uint64_t raw_size = (uint64_t)obs->requested_size;
    bool positive_calloc = false;

    /* Kind-specific payload validation precedes every publication.
     * Overflow is meaningful only for calloc.  A disagreeing overflow
     * flag or product is malformed event identity; an actual product
     * overflow is arithmetic failure. */
    if (obs->kind != OSPREY_ALLOCATOR_CALLOC) {
        if (obs->overflowed || obs->element_count != 0 ||
            obs->element_size != 0) {
            if (g_shared_run != NULL) {
                g_shared_run->bad_identity = 1;
            }
            return;
        }
    } else {
        uint64_t product;
        bool product_overflow = __builtin_mul_overflow(
            (uint64_t)obs->element_count,
            (uint64_t)obs->element_size, &product);
        if (product_overflow) {
            if (g_shared_run != NULL) {
                g_shared_run->bad_arithmetic = 1;
            }
            return;
        }
        if (obs->overflowed || product != raw_size) {
            if (g_shared_run != NULL) {
                g_shared_run->bad_identity = 1;
            }
            return;
        }
        positive_calloc = obs->element_count > 0 && obs->element_size > 0;
    }

    /* A success event always represents a non-NULL allocation object,
     * including zero-size success.  NULL outcomes belong exclusively to
     * the diagnostic path. */
    if (base == 0) {
        if (g_shared_run != NULL) {
            g_shared_run->bad_identity = 1;
        }
        return;
    }
    if (raw_size > INT64_MAX || raw_base > UINT64_MAX - raw_size) {
        if (g_shared_run != NULL) {
            g_shared_run->bad_arithmetic = 1;
        }
        return;
    }
    ProvenanceObject *obj = provenance_lookup_object(object_id, generation);
    if (obj == NULL || obj->state != PROV_OBJ_LIVE || obj->base != base ||
        obj->requested_size != obs->requested_size ||
        obj->alloc_pc != obs->site_pc) {
        if (g_shared_run != NULL) {
            g_shared_run->bad_identity = 1;
        }
        return;
    }
    if (g_heap_instances == NULL) {
        g_heap_instances = g_array_new(FALSE, FALSE, sizeof(HeapInstance));
    }
    /* A new instance even when the numeric base was reused. */
    HeapInstance h;
    memset(&h, 0, sizeof(h));
    h.region.kind = OSPREY_REGION_HEAP_SITE;
    h.region.code_image_id = 0;
    h.region.site_offset = norm_pc;
    h.instance_id = g_next_heap_instance++;
    h.base = base;
    h.size = obs->requested_size;
    h.prov_object_id = object_id;
    h.prov_generation = generation;
    h.live = true;
    g_array_append_val(g_heap_instances, h);

    record_region_instance(&h.region, h.instance_id, base,
                           raw_base, raw_base + raw_size,
                           h.prov_object_id, h.prov_generation);

    /* F05: successful-return requested size. */
    OspreySharedRun *run = g_shared_run;
    if (run != NULL) {
        OspreyMallocFact fact;
        memset(&fact, 0, sizeof(fact));
        fact.site_pc = norm_pc;
        fact.requested_size = raw_size;
        fact.sample_support = 1;
        qemu_mutex_lock(&g_shared_mutex);
        osprey_table_insert_alloc(run, &fact);
        qemu_mutex_unlock(&g_shared_mutex);
    }

    /* Seed the ADDRESS origin of the return register (RAX) so
     * subsequent loads/stores through the pointer emit F02 BaseAddr
     * facts instead of being opaque.  The origin is keyed to this heap
     * instance (offset 0, pointer width) with the already-normalized
     * allocation call site as producer PC. */
    {
        OspreyCpuOriginState *st = osprey_cpu_origin(env);
        memset(&st->regs[R_EAX], 0, sizeof(st->regs[R_EAX]));
        OspreyAddressOrigin *o = &st->regs[R_EAX].address;
        o->valid = 1;
        o->width = (uint8_t)sizeof(target_ulong);
        o->concrete_value = base;
        o->canonical.region = h.region;
        o->canonical.offset = 0;
        o->producer_pc = norm_pc;
        o->prov_object_id = object_id;
        o->prov_generation = generation;
    }

    /* F06 MayArray: only checked positive calloc geometry is evidence.
     * malloc/realloc never emit F06; zero-count/zero-element calloc
     * emits F05 only.  The canonical start is the new heap region at
     * offset zero; instance IDs and raw bases never enter identity. */
    if (run != NULL && obs->kind == OSPREY_ALLOCATOR_CALLOC &&
        positive_calloc) {
        OspreyMayArrayFact mf;
        memset(&mf, 0, sizeof(mf));
        mf.start.region = h.region;
        mf.start.offset = 0;
        mf.element_count = (uint64_t)obs->element_count;
        mf.element_size = (uint64_t)obs->element_size;
        mf.evidence_kind = OSPREY_MAY_ARRAY_CALLOC_GEOMETRY;
        mf.sample_support = 1;
        qemu_mutex_lock(&g_shared_mutex);
        osprey_table_insert_mayarray(run, &mf);
        qemu_mutex_unlock(&g_shared_mutex);
    }
}

void osprey_on_alloc_failure(const OspreyAllocatorObservation *obs) {
    if (obs == NULL) {
        return;
    }
    /* Stable diagnostic only: normalized site, allocator kind,
     * operands, and overflow status.  No shared fact state is touched
     * (no table insert, no sample support, no census). */
    uint64_t norm_pc = 0;
    if (!osprey_normalize_pc(obs->site_pc, &norm_pc)) {
        return;
    }
    log_msg("[osprey] [alloc-failure] [site %llx] [kind %d] [size %llu] "
            "[count %llu] [element %llu] [overflow %d]\n",
             (unsigned long long)norm_pc, (int)obs->kind,
             (unsigned long long)obs->requested_size,
             (unsigned long long)obs->element_count,
             (unsigned long long)obs->element_size,
             obs->overflowed ? 1 : 0);
}

/* Retire the heap instance whose provenance identity matches.  Returns
 * true when an instance was retired. */
static bool heap_retire_by_identity(uint64_t object_id, uint32_t generation) {
    if (g_heap_instances == NULL) return false;
    for (guint i = 0; i < g_heap_instances->len; i++) {
        HeapInstance *h = &g_array_index(g_heap_instances, HeapInstance, i);
        if (h->live && h->prov_object_id == object_id &&
            h->prov_generation == generation) {
            h->live = false;
            return true;
        }
    }
    return false;
}

void osprey_on_free_identity(CPUArchState *env, uint64_t object_id,
                             uint32_t generation, target_ulong site_pc) {
    (void)env;
    (void)site_pc;
    heap_retire_by_identity(object_id, generation);
}

/* ------------------------------------------------------------------ */
/* Access hooks                                                        */
/* ------------------------------------------------------------------ */

static void record_access_fact(OspreySharedRun *run, uint64_t pc,
                               const OspreyChunk *chunk, int is_store,
                               uint32_t op_class) {
    if (run == NULL) return;
    OspreyAccessFact fact;
    memset(&fact, 0, sizeof(fact));
    fact.pc = pc;
    fact.chunk = *chunk;
    fact.dynamic_count = 1;
    fact.sample_support = 1;
    fact.is_store = (uint8_t)(is_store != 0);
    fact.op_class = (uint8_t)op_class;
    qemu_mutex_lock(&g_shared_mutex);
    osprey_table_insert_access(run, &fact);
    qemu_mutex_unlock(&g_shared_mutex);
    run->total_dynamic_observations =
        sat_add_u64(run->total_dynamic_observations, 1);
}

void osprey_on_mem_access(CPUArchState *env, target_ulong addr,
                          uint64_t size, uint64_t pc, uint32_t is_store) {
    osprey_on_mem_access_class(env, addr, size, pc, is_store,
                               0); /* SEM_OP_INTEGER */
}

void osprey_on_mem_access_class(CPUArchState *env, target_ulong addr,
                                uint64_t size, uint64_t pc,
                                uint32_t is_store, uint32_t op_class) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    if (op_class >= SEM_OP_CLASS_COUNT ||
        !sem_op_class_valid[op_class]) {
        st->pending_helper_count = 0;
        memset(&st->ea, 0, sizeof(st->ea));
        st->ea_mode = 0;
        return;
    }
    OspreySharedRun *run = g_shared_run;
    if (run == NULL) {
        st->pending_helper_count = 0;
        memset(&st->ea, 0, sizeof(st->ea));
        st->ea_mode = 0;
        return;
    }

    /* Move the complete EA snapshot into locals and clear every pending
     * field BEFORE any PC/region/mode decision: a fault has no
     * post-success call, and the next set-EA, no-EA event, signal/
     * context replacement, unsupported event, or helper boundary must
     * overwrite/clear the abandoned record. */
    OspreyEASnapshot ea = st->ea;
    memset(&st->ea, 0, sizeof(st->ea));

    /* Normalize the PC against the main image base; facts from
     * out-of-image code (libraries, interpreter) are not part of the
     * main-image model and are skipped entirely. */
    uint64_t norm_pc = 0;
    if (!osprey_normalize_pc(pc, &norm_pc)) {
        return;
    }
    pc = norm_pc;

    /* F02 candidate selection: emit only when the EA decomposition
     * proves exactly one eligible address origin participates in the
     * effective address.  Mode eligibility was already enforced by
     * helper_sem_mem_access (MO_64, no segment override); -2
     * (RIP-relative) is a proven non-GPR address form and never
     * contributes a register origin.  Every mode-eligible failure
     * keeps its valid F01 row; no whole-sample rejection happens here.
     *
     * Accepted forms:
     *  - [base + disp]: base snapshot valid, exact wrapping
     *    reconstruction equals the observed EA;
     *  - [base + index + disp]: base is the SOLE valid origin, index
     *    untagged, SIB shift zero (*1);
     *  - [index + disp] (no base register): index is the sole valid
     *    origin, SIB shift zero.
     *
     * The runtime delta is derived from the accepted origin's concrete
     * value; origin.canonical.offset + delta must equal the accessed
     * chunk offset with checked arithmetic and equal canonical regions.
     * Never choose the numerically nearest register and never fall back
     * from stale provenance to numeric heap lookup. */
    const OspreyAddressOrigin *selected = NULL;
    int selected_reg = -1;
    int64_t delta = 0;

    if (ea.valid) {
        bool base_present = ea.base_reg >= 0 && ea.base_reg < CPU_NB_REGS;
        bool index_present = ea.index_reg >= 0 &&
            ea.index_reg < CPU_NB_REGS;
        bool base_tagged = base_present && ea.base_origin.valid;
        bool index_tagged = index_present && ea.index_origin.valid;

        /* A tagged snapshot with the wrong width, mismatched concrete
         * register value, stale heap identity, or inconsistent non-heap
         * provenance is not an untagged operand.  Reject this F02
         * candidate and invalidate the authoritative channel if the
         * register still carries the exact snapshot. */
        bool base_bad = base_tagged &&
            (ea.base_origin.width != sizeof(target_ulong) ||
             ea.base_origin.concrete_value != ea.base_val ||
             !osprey_address_origin_live(&ea.base_origin));
        bool index_bad = index_tagged &&
            (ea.index_origin.width != sizeof(target_ulong) ||
             ea.index_origin.concrete_value != ea.index_val ||
             !osprey_address_origin_live(&ea.index_origin));
        if (base_bad) {
            origin_invalidate_snapshot(env, ea.base_reg, &ea.base_origin);
        }
        if (index_bad) {
            origin_invalidate_snapshot(env, ea.index_reg, &ea.index_origin);
        }

        bool base_ok = base_tagged && !base_bad;
        bool index_ok = index_tagged && !index_bad;
        if (!base_bad && !index_bad && base_ok && !index_present) {
            /* [base + disp] with no index register at all. */
            target_ulong expect = ea.base_val + (target_ulong)ea.disp;
            if (expect == addr) {
                selected = &ea.base_origin;
                selected_reg = ea.base_reg;
                delta = origin_wrapped_delta(addr, ea.base_val);
            }
        } else if (!base_bad && !index_bad && base_ok && index_present &&
                   !index_ok && ea.scale == 0) {
            /* [base + index + disp]: base is the sole valid origin, the
             * index is untagged, and the SIB shift is zero (*1). */
            target_ulong expect = ea.base_val +
                (target_ulong)ea.index_val + (target_ulong)ea.disp;
            if (expect == addr) {
                selected = &ea.base_origin;
                selected_reg = ea.base_reg;
                delta = origin_wrapped_delta(addr, ea.base_val);
            }
        } else if (!base_bad && !index_bad && !base_present && index_ok &&
                   ea.scale == 0) {
            /* [index + disp]: no architectural base register contributes,
             * the index is the sole valid origin, and the SIB shift is
             * zero. */
            target_ulong expect = ea.index_val + (target_ulong)ea.disp;
            if (expect == addr) {
                selected = &ea.index_origin;
                selected_reg = ea.index_reg;
                delta = origin_wrapped_delta(addr, ea.index_val);
            }
        }
        /* All other forms — no origin, two tagged origins, bad channel,
         * any SIB shift greater than zero, or reconstruction mismatch —
         * emit F01 without F02. */
    }

    /* Resolve the accessed chunk to a canonical region.  Accesses that
     * do not resolve (libraries, anonymous mmap) are ordinary skipped
     * observations, never forced into a region. */
    OspreyRegionId region;
    int64_t off;
    if (!osprey_region_of_addr(env, addr, &region, &off, false)) {
        return;
    }
    OspreyChunk chunk;
    chunk.address.region = region;
    chunk.address.offset = off;
    chunk.size = size;

    record_access_fact(run, pc, &chunk, is_store != 0, op_class);

    if (selected != NULL) {
        /* Canonical region equality + checked offset fold. */
        if (!origin_region_eq(&selected->canonical.region,
                              &chunk.address.region)) {
            selected = NULL;
        } else {
            int64_t folded = 0;
            if (!osprey_check_add(selected->canonical.offset, delta,
                                  &folded)) {
                origin_invalidate_snapshot(env, selected_reg, selected);
                selected = NULL;
            } else if (folded != chunk.address.offset) {
                selected = NULL;
            }
        }
    }

    if (selected != NULL) {
        OspreyBaseFact bf;
        memset(&bf, 0, sizeof(bf));
        bf.pc = pc;
        bf.chunk = chunk;
        bf.base = selected->canonical;
        bf.prov_object_id = selected->prov_object_id;
        bf.prov_generation = selected->prov_generation;
        bf.producer_pc = selected->producer_pc;
        bf.sample_support = 1;
        qemu_mutex_lock(&g_shared_mutex);
        osprey_table_insert_base(run, &bf);
        qemu_mutex_unlock(&g_shared_mutex);
    }
    /* An address outside every modeled region is an ordinary skipped
     * observation (libraries, anonymous mmap), never a sticky error.
     * Stage 2.3 emits no F04 points-to facts from store/load. */
}

/* Modeled byte copies (memcpy/memmove/strcpy family).  Runs only after
 * the model's full success boundary.  Consumer order (Stage 2.4):
 *  1. reject zero/wrapping ranges (ordinary no-op, no mutation);
 *  2. snapshot every live aligned ADDRESS source slot fully contained
 *     in the copy interval BEFORE touching destination shadow
 *     (overlapping memmove);
 *  3. validate saved source bytes and heap identity; discard stale
 *     source slots;
 *  4. invalidate every destination-overlapping slot;
 *  5. publish one F03 for the full copied interval only when both
 *     complete source and destination intervals canonicalize;
 *  6. relocate each snapshotted ADDRESS slot by dst + (slot - src) only
 *     when the resulting complete pointer slot is nonwrapping and
 *     aligned;
 *  7. install relocated slots after invalidation;
 *  8. publish F04 for each relocated pointer slot whose destination
 *     canonicalizes.
 * Source/destination outside modeled regions omit the corresponding
 * F03/F04 but still perform destination invalidation and any sound
 * ADDRESS-shadow relocation.  Never splits a large F03 into byte rows. */
void osprey_on_mem_copy(CPUArchState *env, target_ulong src,
                        target_ulong dst, target_ulong size) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    if (size == 0) {
        return;
    }
    if (dst + (size - 1) < dst || src + (size - 1) < src) {
        /* Wrapping copy interval: no exact overlap can be represented.
         * Clear the destination shadow conservatively; no fact. */
        if (st->mem_slots != NULL) {
            g_hash_table_remove_all(st->mem_slots);
        }
        return;
    }
    /* 1. Snapshot every source slot fully contained in [src,src+size)
     * before destination invalidation.  The sparse shadow already
     * bounds this allocation; a fixed local cap would silently drop
     * valid tags and even mutate a disjoint source range. */
    typedef struct OspreyCopiedSlot {
        target_ulong addr;
        OspreyMemAddressOrigin slot;
        bool valid;
    } OspreyCopiedSlot;
    GArray *src_slots = g_array_sized_new(
        FALSE, FALSE, sizeof(OspreyCopiedSlot),
        st->mem_slots != NULL ? g_hash_table_size(st->mem_slots) : 0);
    if (st->mem_slots != NULL && size >= OSPREY_SHADOW_ALIGN) {
        GHashTableIter it;
        gpointer key, value;
        g_hash_table_iter_init(&it, st->mem_slots);
        while (g_hash_table_iter_next(&it, &key, &value)) {
            target_ulong slot_addr = (target_ulong)GPOINTER_TO_SIZE(key);
            if (slot_addr >= src &&
                slot_addr - src <= size - OSPREY_SHADOW_ALIGN) {
                OspreyMemAddressOrigin *origin = value;
                OspreyCopiedSlot saved;
                memset(&saved, 0, sizeof(saved));
                saved.addr = slot_addr;
                saved.valid = origin != NULL && origin->valid != 0;
                if (saved.valid) {
                    saved.slot = *origin;
                }
                g_array_append_val(src_slots, saved);
            }
        }
    }
    /* 2. Validate saved source slots: heap identities must still be
     * live.  The model preflight proved all source bytes readable and
     * all destination bytes writable before this event, so the saved
     * concrete values are authoritative without a guest re-read;
     * a later load still performs the normal byte/value/liveness
     * consistency check.  Stale source slots are removed from the
     * shadow so later coincidental bytes cannot resurrect them. */
    for (guint i = 0; i < src_slots->len; i++) {
        OspreyCopiedSlot *saved = &g_array_index(
            src_slots, OspreyCopiedSlot, i);
        if (!saved->valid) {
            continue;
        }
        if (saved->slot.width != sizeof(target_ulong)) {
            saved->valid = false;
            if (st->mem_slots != NULL) {
                g_hash_table_remove(st->mem_slots,
                                    GSIZE_TO_POINTER(saved->addr));
            }
            continue;
        }
        if (saved->slot.prov_object_id != 0) {
            OspreyAddressOrigin tmp;
            memset(&tmp, 0, sizeof(tmp));
            tmp.valid = 1;
            tmp.width = saved->slot.width;
            tmp.concrete_value = saved->slot.concrete_value;
            tmp.canonical = saved->slot.canonical;
            tmp.prov_object_id = saved->slot.prov_object_id;
            tmp.prov_generation = saved->slot.prov_generation;
            if (!origin_heap_prov_ok(&tmp)) {
                saved->valid = false;
                if (st->mem_slots != NULL) {
                    g_hash_table_remove(st->mem_slots,
                                        GSIZE_TO_POINTER(saved->addr));
                }
            }
        }
    }
    /* 3. Invalidate every destination-overlapping slot. */
    origin_invalidate_mem_range(st, dst, size);
    OspreySharedRun *run = g_shared_run;
    /* 4. One exact F03 for the full copied interval. */
    if (run != NULL) {
        OspreyChunk s_chunk, d_chunk;
        if (osprey_chunk_of_interval(env, src, size, &s_chunk) &&
            osprey_chunk_of_interval(env, dst, size, &d_chunk)) {
            OspreyCopyFact fact;
            memset(&fact, 0, sizeof(fact));
            fact.source = s_chunk;
            fact.destination = d_chunk;
            fact.sample_support = 1;
            qemu_mutex_lock(&g_shared_mutex);
            osprey_table_insert_copy(run, &fact);
            qemu_mutex_unlock(&g_shared_mutex);
        }
    }
    /* 5-8. Relocate each validated source slot.  The model proved the
     * copied bytes, so the validated source slot's concrete value is
     * authoritative without requiring destination bytes to have
     * changed before the real modeled call returns.  A later load
     * still performs the normal byte/value/liveness consistency check. */
    for (guint i = 0; i < src_slots->len; i++) {
        OspreyCopiedSlot *saved = &g_array_index(
            src_slots, OspreyCopiedSlot, i);
        if (!saved->valid) {
            continue;
        }
        target_ulong off = saved->addr - src;
        target_ulong dst_slot = dst + off;
        if (dst_slot + OSPREY_SHADOW_ALIGN - 1 < dst_slot) {
            continue; /* nonwrapping requirement */
        }
        if ((dst_slot & (OSPREY_SHADOW_ALIGN - 1)) != 0 ||
            st->mem_slots == NULL) {
            continue; /* unaligned/no-shadow relocation rejected */
        }
        OspreyMemAddressOrigin *slot =
            g_new0(OspreyMemAddressOrigin, 1);
        slot->valid = 1;
        slot->width = saved->slot.width;
        slot->canonical = saved->slot.canonical;
        slot->concrete_value = saved->slot.concrete_value;
        slot->prov_object_id = saved->slot.prov_object_id;
        slot->prov_generation = saved->slot.prov_generation;
        g_hash_table_replace(st->mem_slots, GSIZE_TO_POINTER(dst_slot),
                             slot);
        if (run != NULL) {
            OspreyChunk cell;
            if (osprey_chunk_of_interval(env, dst_slot,
                                         sizeof(target_ulong), &cell)) {
                OspreyPointsToFact fact;
                memset(&fact, 0, sizeof(fact));
                fact.pointer_chunk = cell;
                fact.target = slot->canonical;
                fact.sample_support = 1;
                fact.weak_numeric_evidence = 0;
                qemu_mutex_lock(&g_shared_mutex);
                osprey_table_insert_points(run, &fact);
                qemu_mutex_unlock(&g_shared_mutex);
            }
        }
    }
    g_array_free(src_slots, TRUE);
}

/* Sticky error diagnostics (child and parent side). */
void osprey_log_sticky(const OspreySharedRun *run, const char *tag) {
    if (run == NULL) return;
    log_msg("[osprey] [facts] [%s] [sample %u] [overflow %u] "
            "[bad-region %u] [bad-arith %u] [bad-identity %u] "
            "[unsupported %u] "
            "[first-kind %u] [first-hash %lx]\n",
            tag, run->sample_id, run->overflow, run->bad_region,
            run->bad_arithmetic, run->bad_identity,
            run->unsupported_execution,
            run->first_dropped_kind,
            (unsigned long)run->first_dropped_hash);
}

/* ------------------------------------------------------------------ */
/* Parent-side merge + analysis entry                                  */
/* ------------------------------------------------------------------ */

/* ------------------------------------------------------------------ */
/* Parent-side merge + analysis entry                                  */
/* ------------------------------------------------------------------ */

/* ------------------------------------------------------------------ */
/* Fail-closed analysis transaction (Stage 0)                          */
/* ------------------------------------------------------------------ */

/* Begin a new baseline analysis transaction.  The status is sticky:
 * once non-OK it never returns to OK until the next complete baseline
 * analysis.  Staged graph/model pointers start NULL. */
void osprey_tx_begin(OspreyContext *ctx) {
    if (ctx == NULL) return;
    osprey_tx_abort(ctx);
    ctx->tx_status = OSPREY_OK;
    ctx->tx_stage = NULL;
    ctx->tx_reason = NULL;
    ctx->tx_model_ready = false;
    ctx->last_status = OSPREY_OK;
}

/* Reject the current transaction: record the first failure (status,
 * stage, reason) and emit exactly one stable rejection row.  Later
 * failures keep the first recorded status/stage. */
void osprey_tx_reject(OspreyContext *ctx, OspreyStatus st,
                      const char *stage, const char *reason) {
    if (ctx == NULL) return;
    if (ctx->tx_status == OSPREY_OK) {
        ctx->tx_status = st;
        ctx->tx_stage = stage;
        ctx->tx_reason = reason;
        ctx->tx_model_ready = false;
        ctx->last_status = st;
        log_msg("[osprey] [reject] [status %d] [stage %s] [reason %s]\n",
                (int)st, stage != NULL ? stage : "?",
                reason != NULL ? reason : "?");
    }
}

bool osprey_tx_ok(const OspreyContext *ctx) {
    return ctx != NULL && ctx->tx_status == OSPREY_OK;
}

OspreyStatus osprey_tx_status(const OspreyContext *ctx) {
    return ctx != NULL ? ctx->tx_status : OSPREY_DISABLED;
}

const char *osprey_tx_stage(const OspreyContext *ctx) {
    return ctx != NULL ? ctx->tx_stage : NULL;
}

/* Commit the staged graph and model.  Only called when the whole
 * transaction is OSPREY_OK; the previous committed model is destroyed
 * only after the new one is fully built and validated. */
void osprey_tx_install(OspreyContext *ctx) {
    if (ctx == NULL) return;
    if (ctx->staged_graph != NULL) {
        if (ctx->graph != NULL) {
            osprey_graph_free(ctx->graph);
        }
        ctx->graph = ctx->staged_graph;
        ctx->staged_graph = NULL;
    }
    if (ctx->staged_model != NULL) {
        if (ctx->model != NULL) {
            osprey_model_free(ctx->model);
        }
        ctx->model = ctx->staged_model;
        ctx->staged_model = NULL;
    }
    ctx->tx_model_ready = ctx->graph != NULL && ctx->model != NULL;
    ctx->last_status = OSPREY_OK;
}

/* Abort the current transaction: destroy staged state.  The committed
 * graph/model are kept but hidden (osprey_model() returns NULL while
 * tx_status is non-OK); they are replaced by the next successful
 * transaction or freed by osprey_free().  Callers must detach
 * ctx->graph from ctx->staged_graph before aborting. */
void osprey_tx_abort(OspreyContext *ctx) {
    if (ctx == NULL) return;
    if (ctx->staged_graph != NULL) {
        osprey_graph_free(ctx->staged_graph);
        ctx->staged_graph = NULL;
    }
    if (ctx->staged_model != NULL) {
        osprey_model_free(ctx->staged_model);
        ctx->staged_model = NULL;
    }
    ctx->last_status = ctx->tx_status;
}

/* Prefix record-count field for a prefix table (validation). */
static uint32_t osprey_prefix_used_field(const OspreySharedRun *run,
                                         int table) {
    switch (table) {
    case OSPREY_TABLE_PREFIX_ACCESS: return run->prefix_access_used;
    case OSPREY_TABLE_PREFIX_BASE: return run->prefix_base_used;
    case OSPREY_TABLE_PREFIX_COPY: return run->prefix_copy_used;
    case OSPREY_TABLE_PREFIX_POINTS: return run->prefix_points_used;
    case OSPREY_TABLE_PREFIX_ALLOC: return run->prefix_alloc_used;
    case OSPREY_TABLE_PREFIX_MAYARR: return run->prefix_mayarray_used;
    default: return run->prefix_region_used;
    }
}

static bool osprey_record_support_valid(int table, const void *record) {
    switch (table) {
    case OSPREY_TABLE_ACCESS:
    case OSPREY_TABLE_PREFIX_ACCESS:
        return ((const OspreyAccessFact *)record)->sample_support == 1;
    case OSPREY_TABLE_BASE:
    case OSPREY_TABLE_PREFIX_BASE:
        return ((const OspreyBaseFact *)record)->sample_support == 1;
    case OSPREY_TABLE_COPY:
    case OSPREY_TABLE_PREFIX_COPY:
        return ((const OspreyCopyFact *)record)->sample_support == 1;
    case OSPREY_TABLE_POINTS:
    case OSPREY_TABLE_PREFIX_POINTS:
        return ((const OspreyPointsToFact *)record)->sample_support == 1;
    case OSPREY_TABLE_ALLOC:
    case OSPREY_TABLE_PREFIX_ALLOC:
        return ((const OspreyMallocFact *)record)->sample_support == 1;
    case OSPREY_TABLE_MAYARR:
    case OSPREY_TABLE_PREFIX_MAYARR:
        return ((const OspreyMayArrayFact *)record)->sample_support == 1;
    default:
        return ((const OspreyRegionInstance *)record)->sample_support == 1;
    }
}

static bool osprey_run_population_valid(const OspreySharedRun *run) {
    static const int tables[] = {
        OSPREY_TABLE_ACCESS, OSPREY_TABLE_BASE, OSPREY_TABLE_COPY,
        OSPREY_TABLE_POINTS, OSPREY_TABLE_ALLOC, OSPREY_TABLE_MAYARR,
        OSPREY_TABLE_REGION,
    };
    for (size_t i = 0; i < G_N_ELEMENTS(tables); i++) {
        OspreyRunIter it;
        const void *record;
        uint32_t count = 0;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = tables[i];
        while (osprey_run_iter_next(&it, &record)) {
            if (!osprey_record_support_valid(tables[i], record)) {
                return false;
            }
            count++;
        }
        if (count != table_used_count(run, tables[i])) return false;
        /* Prefix family: occupied slots must equal the recorded count. */
        int pref = OSPREY_TABLE_PREFIX_ACCESS + (int)i;
        count = 0;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = pref;
        while (osprey_run_iter_next(&it, &record)) {
            if (!osprey_record_support_valid(pref, record)) {
                return false;
            }
            count++;
        }
        if (count != osprey_prefix_used_field(run, pref)) {
            return false;
        }
    }
    /* Census tables: occupied slots must equal the used counters. */
    {
        const int census_tables[2] = { OSPREY_TABLE_CENSUS_CHUNK,
                                       OSPREY_TABLE_CENSUS_REGION };
        const uint32_t *census_used[2] = { &run->census_chunk_used,
                                           &run->census_region_used };
        for (size_t i = 0; i < G_N_ELEMENTS(census_tables); i++) {
            OspreyRunIter it;
            const void *record;
            uint32_t count = 0;
            memset(&it, 0, sizeof(it));
            it.run = run;
            it.table = census_tables[i];
            while (osprey_run_iter_next(&it, &record)) {
                count++;
            }
            if (count != *census_used[i]) return false;
        }
    }
    uint64_t prefix_count = (uint64_t)run->prefix_access_used +
        run->prefix_base_used + run->prefix_copy_used +
        run->prefix_points_used + run->prefix_alloc_used +
        run->prefix_mayarray_used + run->prefix_region_used;
    if (run->prefix_frozen) {
        if (run->prefix_facts_count != prefix_count) return false;
    } else if (prefix_count != 0 || run->prefix_facts_count != 0 ||
               run->total_dynamic_prefix != 0) {
        return false;
    }
    return true;
}

/* Open-addressed presence probe (mirrors run_table_insert probing:
 * linear probing with growing step; an empty slot terminates).  Used
 * for same-sample dedup between the frozen prefix and child suffix
 * families during the parent merge. */
static bool run_table_contains(const OspreySharedRun *run, int table,
                               const void *rec, HashFn hash, VerifyFn eq) {
    uint32_t cap = table_cap_of(run, table);
    if (cap == 0) return false;
    uint8_t *base = osprey_run_table((OspreySharedRun *)run, table);
    size_t rec_size = table_record_size_of(table);
    uint64_t h = hash(rec);
    uint32_t slot = (uint32_t)(h % cap);
    uint32_t step = 1;
    while (step <= cap) {
        uint8_t *ent = base + (size_t)slot * rec_size;
        bool empty = true;
        for (size_t i = 0; i < rec_size; i++) {
            if (ent[i] != 0) {
                empty = false;
                break;
            }
        }
        if (empty) {
            return false;
        }
        if (eq(ent, rec)) {
            return true;
        }
        slot = (slot + step) % cap;
        step++;
    }
    return false;
}

/* Stage 2.5 fixed-record semantics.  Production emits F05 and F06
 * together from one validated calloc success, but the parent still
 * validates child transport before committing it or exposing it to the
 * signed canonical-offset rule code. */
static bool osprey_run_allocator_facts_valid(const OspreySharedRun *run) {
    static const int alloc_tables[] = {
        OSPREY_TABLE_ALLOC, OSPREY_TABLE_PREFIX_ALLOC,
    };
    static const int may_tables[] = {
        OSPREY_TABLE_MAYARR, OSPREY_TABLE_PREFIX_MAYARR,
    };

    for (size_t i = 0; i < G_N_ELEMENTS(alloc_tables); i++) {
        OspreyRunIter it = { .run = run, .table = alloc_tables[i] };
        const void *record;
        while (osprey_run_iter_next(&it, &record)) {
            const OspreyMallocFact *f = record;
            if (f->requested_size > INT64_MAX || f->reserved != 0) {
                return false;
            }
        }
    }

    for (size_t i = 0; i < G_N_ELEMENTS(may_tables); i++) {
        OspreyRunIter it = { .run = run, .table = may_tables[i] };
        const void *record;
        while (osprey_run_iter_next(&it, &record)) {
            const OspreyMayArrayFact *f = record;
            uint64_t total;
            if (f->start.region.kind != OSPREY_REGION_HEAP_SITE ||
                f->start.region.code_image_id != 0 ||
                f->start.offset != 0 || f->element_count == 0 ||
                f->element_size == 0 ||
                f->evidence_kind != OSPREY_MAY_ARRAY_CALLOC_GEOMETRY ||
                __builtin_mul_overflow(f->element_count, f->element_size,
                                       &total) ||
                total > INT64_MAX) {
                return false;
            }
            OspreyMallocFact alloc;
            memset(&alloc, 0, sizeof(alloc));
            alloc.site_pc = f->start.region.site_offset;
            alloc.requested_size = total;
            alloc.sample_support = 1;
            if (!run_table_contains(run, OSPREY_TABLE_ALLOC, &alloc,
                                    (HashFn)osprey_alloc_hash,
                                    (VerifyFn)osprey_alloc_eq) &&
                !run_table_contains(run, OSPREY_TABLE_PREFIX_ALLOC, &alloc,
                                    (HashFn)osprey_alloc_hash,
                                    (VerifyFn)osprey_alloc_eq)) {
                return false;
            }
        }
    }
    return true;
}

/* Validate the maintained unique-fact counter against the actual
 * `prefix ∪ suffix` population.  A corrupted or stale counter must not
 * weaken max_facts or reject a valid duplicate at the cap. */
static bool osprey_run_fact_count_valid(const OspreySharedRun *run) {
    static const int tables[] = {
        OSPREY_TABLE_ACCESS, OSPREY_TABLE_BASE, OSPREY_TABLE_COPY,
        OSPREY_TABLE_POINTS, OSPREY_TABLE_ALLOC, OSPREY_TABLE_MAYARR,
        OSPREY_TABLE_REGION,
    };
    static const HashFn hashes[] = {
        (HashFn)osprey_access_hash, (HashFn)osprey_base_hash,
        (HashFn)osprey_copy_hash, (HashFn)osprey_points_hash,
        (HashFn)osprey_alloc_hash, (HashFn)osprey_mayarray_hash,
        (HashFn)osprey_region_instance_hash,
    };
    static const VerifyFn equals[] = {
        (VerifyFn)osprey_access_eq, (VerifyFn)osprey_base_eq,
        (VerifyFn)osprey_copy_eq, (VerifyFn)osprey_points_eq,
        (VerifyFn)osprey_alloc_eq, (VerifyFn)osprey_mayarray_eq,
        (VerifyFn)osprey_region_instance_eq,
    };
    uint64_t count = 0;
    for (size_t i = 0; i < G_N_ELEMENTS(tables); i++) {
        int prefix = OSPREY_TABLE_PREFIX_ACCESS + (int)i;
        count += osprey_prefix_used_field(run, prefix);
        OspreyRunIter it;
        const void *record;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = tables[i];
        while (osprey_run_iter_next(&it, &record)) {
            if (!run->prefix_frozen ||
                !run_table_contains(run, prefix, record,
                                    hashes[i], equals[i])) {
                count++;
            }
        }
    }
    return count == run->total_facts_count;
}

/* Build the paper-level Access projection before the sample is merged.
 * F01 identity deliberately keeps direction and operation class, while
 * Access(i,v,k) does not.  The temporary map therefore keys only on
 * (pc,complete chunk), sums all dynamic observations with saturation, and
 * records one sample presence regardless of how many F01 rows supplied it. */
static GArray *build_sample_logical_accesses(const OspreySharedRun *run)
{
    GArray *rows = g_array_new(FALSE, FALSE, sizeof(OspreyLogicalAccess));
    GHashTable *index = g_hash_table_new_full(
        osprey_key_hash, osprey_key_equal, osprey_key_free, NULL);
    const int tables[] = { OSPREY_TABLE_ACCESS,
                           OSPREY_TABLE_PREFIX_ACCESS };

    for (size_t t = 0; t < G_N_ELEMENTS(tables); t++) {
        OspreyRunIter it;
        const void *record;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = tables[t];
        while (osprey_run_iter_next(&it, &record)) {
            const OspreyAccessFact *fact = record;
            OspreyKey key = osprey_logical_access_key(fact->pc,
                                                       &fact->chunk);
            gpointer found = g_hash_table_lookup(index, &key);
            if (found != NULL) {
                OspreyLogicalAccess *row = &g_array_index(
                    rows, OspreyLogicalAccess,
                    (guint)(GPOINTER_TO_SIZE(found) - 1));
                row->dynamic_count = sat_add_u32(row->dynamic_count,
                                                 fact->dynamic_count);
                continue;
            }
            OspreyLogicalAccess row;
            memset(&row, 0, sizeof(row));
            row.pc = fact->pc;
            row.chunk = fact->chunk;
            row.dynamic_count = fact->dynamic_count;
            row.sample_support = 1;
            g_array_append_val(rows, row);
            g_hash_table_insert(index, osprey_key_new(&key),
                                GSIZE_TO_POINTER((gsize)rows->len));
        }
    }
    g_hash_table_destroy(index);
    g_array_sort(rows, osprey_logical_access_compare);
    return rows;
}

static void merge_logical_accesses(OspreyContext *ctx,
                                   const GArray *sample_rows)
{
    for (guint i = 0; i < sample_rows->len; i++) {
        const OspreyLogicalAccess *sample = &g_array_index(
            sample_rows, OspreyLogicalAccess, i);
        bool found = false;
        for (guint j = 0; j < ctx->logical_access_facts->len; j++) {
            OspreyLogicalAccess *committed = &g_array_index(
                ctx->logical_access_facts, OspreyLogicalAccess, j);
            if (osprey_logical_access_equal(committed, sample)) {
                committed->dynamic_count = sat_add_u32(
                    committed->dynamic_count, sample->dynamic_count);
                committed->sample_support = sat_add_u32(
                    committed->sample_support, 1);
                found = true;
                break;
            }
        }
        if (!found) {
            OspreyLogicalAccess copy = *sample;
            copy.sample_support = 1;
            g_array_append_val(ctx->logical_access_facts, copy);
        }
    }
    g_array_sort(ctx->logical_access_facts, osprey_logical_access_compare);
}

/* Merge one fact family from a table (suffix or prefix family) into
 * the committed parent arrays.  `sample_from` is the parent-array index
 * where this sample's first pass started: a record equal to an entry
 * at/after that index is a same-sample duplicate (prefix∩suffix) and
 * contributes no additional support (Boolean per sample); a record
 * matching an earlier committed entry adds exactly one support.  The
 * prefix family is merged first (its records are the sample's first
 * occurrence); the suffix pass then skips the support increment for
 * records already present in the prefix (`peer` table).  Dynamic/weak
 * counters are always summed with saturation (a fact observed both
 * before the snapshot and in the child suffix is one sample with the
 * sum of its observations). */
static void merge_access_family(OspreyContext *ctx, const OspreySharedRun *run,
                                int table, int peer, guint sample_from) {
    OspreyRunIter it;
    const void *rec;
    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = table;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyAccessFact *f = rec;
        bool found = false;
        for (guint i = 0; i < ctx->access_facts->len; i++) {
            OspreyAccessFact *d = &g_array_index(ctx->access_facts,
                                                 OspreyAccessFact, i);
            if (osprey_access_eq(d, f)) {
                d->dynamic_count = sat_add_u32(d->dynamic_count,
                                               f->dynamic_count);
                if (i < sample_from && f->sample_support != 0 &&
                    (peer < 0 || !run_table_contains(run, peer, f,
                                        (HashFn)osprey_access_hash,
                                        (VerifyFn)osprey_access_eq))) {
                    d->sample_support = sat_add_u32(d->sample_support, 1);
                }
                found = true;
                break;
            }
        }
        if (!found) {
            g_array_append_val(ctx->access_facts, *f);
        }
    }
}

static void merge_base_family(OspreyContext *ctx, const OspreySharedRun *run,
                              int table, int peer, guint sample_from) {
    OspreyRunIter it;
    const void *rec;
    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = table;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyBaseFact *f = rec;
        bool found = false;
        for (guint i = 0; i < ctx->base_facts->len; i++) {
            OspreyBaseFact *d = &g_array_index(ctx->base_facts,
                                               OspreyBaseFact, i);
            if (osprey_base_eq(d, f)) {
                if (i < sample_from && f->sample_support != 0 &&
                    (peer < 0 || !run_table_contains(run, peer, f,
                                        (HashFn)osprey_base_hash,
                                        (VerifyFn)osprey_base_eq))) {
                    d->sample_support = sat_add_u32(d->sample_support, 1);
                }
                /* Deterministic audit metadata: retain the numerically
                 * smallest producer PC (including zero) so insertion
                 * order (prefix/suffix, repeated paths) cannot alter the
                 * canonical dump. */
                if (f->producer_pc < d->producer_pc) {
                    d->producer_pc = f->producer_pc;
                }
                found = true;
                break;
            }
        }
        if (!found) {
            g_array_append_val(ctx->base_facts, *f);
        }
    }
}

static void merge_copy_facts(OspreyContext *ctx, const OspreySharedRun *run,
                             int table, int peer, guint sample_from) {
    OspreyRunIter it;
    const void *rec;
    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = table;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyCopyFact *f = rec;
        bool found = false;
        for (guint i = 0; i < ctx->copy_facts->len; i++) {
            OspreyCopyFact *d = &g_array_index(ctx->copy_facts,
                                               OspreyCopyFact, i);
            if (osprey_copy_eq(d, f)) {
                if (i < sample_from && f->sample_support != 0 &&
                    (peer < 0 || !run_table_contains(run, peer, f,
                                        (HashFn)osprey_copy_hash,
                                        (VerifyFn)osprey_copy_eq))) {
                    d->sample_support = sat_add_u32(d->sample_support, 1);
                }
                found = true;
                break;
            }
        }
        if (!found) {
            g_array_append_val(ctx->copy_facts, *f);
        }
    }
}

static void merge_points_facts(OspreyContext *ctx,
                               const OspreySharedRun *run,
                               int table, int peer, guint sample_from) {
    OspreyRunIter it;
    const void *rec;
    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = table;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyPointsToFact *f = rec;
        bool found = false;
        for (guint i = 0; i < ctx->points_facts->len; i++) {
            OspreyPointsToFact *d = &g_array_index(ctx->points_facts,
                                                   OspreyPointsToFact, i);
            if (osprey_points_eq(d, f)) {
                d->weak_numeric_evidence = sat_add_u32(
                    d->weak_numeric_evidence, f->weak_numeric_evidence);
                if (i < sample_from && f->sample_support != 0 &&
                    (peer < 0 || !run_table_contains(run, peer, f,
                                        (HashFn)osprey_points_hash,
                                        (VerifyFn)osprey_points_eq))) {
                    d->sample_support = sat_add_u32(d->sample_support, 1);
                }
                found = true;
                break;
            }
        }
        if (!found) {
            g_array_append_val(ctx->points_facts, *f);
        }
    }
}

static void merge_alloc_facts(OspreyContext *ctx,
                              const OspreySharedRun *run,
                              int table, int peer, guint sample_from) {
    OspreyRunIter it;
    const void *rec;
    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = table;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyMallocFact *f = rec;
        bool found = false;
        for (guint i = 0; i < ctx->alloc_facts->len; i++) {
            OspreyMallocFact *d = &g_array_index(ctx->alloc_facts,
                                                 OspreyMallocFact, i);
            if (osprey_alloc_eq(d, f)) {
                if (i < sample_from && f->sample_support != 0 &&
                    (peer < 0 || !run_table_contains(run, peer, f,
                                        (HashFn)osprey_alloc_hash,
                                        (VerifyFn)osprey_alloc_eq))) {
                    d->sample_support = sat_add_u32(d->sample_support, 1);
                }
                found = true;
                break;
            }
        }
        if (!found) {
            g_array_append_val(ctx->alloc_facts, *f);
        }
    }
}

static void merge_mayarray_facts(OspreyContext *ctx,
                                 const OspreySharedRun *run,
                                 int table, int peer, guint sample_from) {
    OspreyRunIter it;
    const void *rec;
    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = table;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyMayArrayFact *f = rec;
        bool found = false;
        for (guint i = 0; i < ctx->mayarray_facts->len; i++) {
            OspreyMayArrayFact *d = &g_array_index(ctx->mayarray_facts,
                                                   OspreyMayArrayFact, i);
            if (osprey_mayarray_eq(d, f)) {
                if (i < sample_from && f->sample_support != 0 &&
                    (peer < 0 || !run_table_contains(run, peer, f,
                                        (HashFn)osprey_mayarray_hash,
                                        (VerifyFn)osprey_mayarray_eq))) {
                    d->sample_support = sat_add_u32(d->sample_support, 1);
                }
                found = true;
                break;
            }
        }
        if (!found) {
            g_array_append_val(ctx->mayarray_facts, *f);
        }
    }
}

static void merge_region_instances(OspreyContext *ctx,
                                   const OspreySharedRun *run,
                                   int table, int peer, guint sample_from) {
    OspreyRunIter it;
    const void *rec;
    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = table;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyRegionInstance *f = rec;
        bool found = false;
        for (guint i = 0; i < ctx->region_instances->len; i++) {
            OspreyRegionInstance *d = &g_array_index(ctx->region_instances,
                                                     OspreyRegionInstance, i);
            if (osprey_region_instance_eq(d, f)) {
                if (f->raw_min < d->raw_min) d->raw_min = f->raw_min;
                if (f->raw_max > d->raw_max) d->raw_max = f->raw_max;
                if (i < sample_from && f->sample_support != 0 &&
                    (peer < 0 || !run_table_contains(run, peer, f,
                                        (HashFn)osprey_region_instance_hash,
                                        (VerifyFn)osprey_region_instance_eq))) {
                    d->sample_support = sat_add_u32(d->sample_support, 1);
                }
                found = true;
                break;
            }
        }
        if (!found) {
            g_array_append_val(ctx->region_instances, *f);
        }
    }
}

/* Merge one completed sample (patch-0/iter-1 child run) into the
 * committed parent tables.  The sample is `prefix ∪ baseline-child`:
 * both families are iterated; duplicates merge support in place and the
 * merged record keeps Boolean per-sample support (one per unique
 * committed sample).  Returns OSPREY_INCOMPLETE_FACTS when the sample
 * overflowed (the model must not be installed from incomplete facts). */
OspreyStatus osprey_parent_merge_sample(OspreyContext *ctx,
                                         const OspreySharedRun *run) {
    if (ctx == NULL || run == NULL) return OSPREY_DISABLED;

    /* The merge opens the analysis transaction: the status is sticky
     * from here until the next complete baseline analysis. */
    osprey_tx_begin(ctx);

    /* Validate the whole run before appending anything: a malformed or
     * overflowed sample must not leave a half-merged transaction. */
    if (run->version != OSPREY_SHARED_VERSION) {
        osprey_tx_reject(ctx, OSPREY_INCOMPLETE_FACTS, "merge",
                         "shared-run version mismatch");
        return OSPREY_INCOMPLETE_FACTS;
    }
    if (run->overflow) {
        osprey_log_sticky(run, "incomplete");
        osprey_tx_reject(ctx, OSPREY_INCOMPLETE_FACTS, "merge",
                         "shared-table overflow");
        return OSPREY_INCOMPLETE_FACTS;
    }
    if (run->bad_arithmetic) {
        osprey_log_sticky(run, "bad-arithmetic");
        osprey_tx_reject(ctx, OSPREY_INCOMPLETE_FACTS, "merge",
                         ctx->pre_sample_fatal && ctx->pre_sample_reason != NULL
                             ? ctx->pre_sample_reason
                             : "checked arithmetic failed");
        return OSPREY_INCOMPLETE_FACTS;
    }
    if (run->bad_identity) {
        osprey_log_sticky(run, "bad-identity");
        osprey_tx_reject(ctx, OSPREY_INCOMPLETE_FACTS, "merge",
                         "provenance identity mismatch");
        return OSPREY_INCOMPLETE_FACTS;
    }
    if (run->unsupported_execution) {
        osprey_tx_reject(ctx, OSPREY_UNSUPPORTED_EXECUTION, "merge",
                         "unsupported guest execution");
        return OSPREY_UNSUPPORTED_EXECUTION;
    }
    if (!osprey_shared_run_layout_valid(&ctx->config, run)) {
        osprey_tx_reject(ctx, OSPREY_INCOMPLETE_FACTS, "merge",
                         "shared-run capacity mismatch");
        return OSPREY_INCOMPLETE_FACTS;
    }
    if (run->access_used > run->access_cap ||
        run->base_used > run->base_cap ||
        run->copy_used > run->copy_cap ||
        run->points_used > run->points_cap ||
        run->alloc_used > run->alloc_cap ||
        run->mayarray_used > run->mayarray_cap ||
        run->region_used > run->region_cap ||
        run->census_chunk_used > run->census_chunk_cap ||
        run->census_region_used > run->census_region_cap) {
        osprey_tx_reject(ctx, OSPREY_INCOMPLETE_FACTS, "merge",
                         "used exceeds capacity");
        return OSPREY_INCOMPLETE_FACTS;
    }
    /* The child-side unique-fact cap (max_facts) is sticky: a sample
     * that hit the cap must not install a model from partial facts. */
    if (run->total_facts_count > run->max_facts_cfg) {
        osprey_log_sticky(run, "facts-cap");
        osprey_tx_reject(ctx, OSPREY_INCOMPLETE_FACTS, "merge",
                         "max_facts exceeded");
        return OSPREY_INCOMPLETE_FACTS;
    }
    if (!osprey_run_population_valid(run)) {
        osprey_tx_reject(ctx, OSPREY_INCOMPLETE_FACTS, "merge",
                         "used count does not match table population");
        return OSPREY_INCOMPLETE_FACTS;
    }
    if (!osprey_run_fact_count_valid(run)) {
        osprey_tx_reject(ctx, OSPREY_INCOMPLETE_FACTS, "merge",
                         "unique fact count does not match population");
        return OSPREY_INCOMPLETE_FACTS;
    }
    if (!osprey_run_allocator_facts_valid(run)) {
        osprey_tx_reject(ctx, OSPREY_INCOMPLETE_FACTS, "merge",
                         "invalid allocator fact record");
        return OSPREY_INCOMPLETE_FACTS;
    }

    /* Construct this before mutating any committed array.  The full
     * shared-run validation above is the complete rejection boundary for
     * the sample; the derived table is committed alongside the fact
     * families below. */
    GArray *sample_logical_accesses = build_sample_logical_accesses(run);

    /* Merge `prefix ∪ suffix` as exactly one unmodified sample: iterate
     * the suffix family first, then the frozen prefix family.  A record
     * present in both parts is the same fact within this sample: it
     * contributes one support (never two) and its dynamic counts are
     * summed (prefix observations + suffix observations).  `sample_from`
     * marks the parent-array index range appended by this sample's
     * suffix pass; a prefix record matching one of those entries is a
     * same-sample duplicate and contributes nothing more.  Records
     * matching entries committed by earlier samples add exactly one
     * support (one per unique committed sample).  All counters are
     * checked/saturating. */

    /* Access facts. */
    {
        guint sample_from = ctx->access_facts->len;
        merge_access_family(ctx, run, OSPREY_TABLE_ACCESS, -1, sample_from);
        merge_access_family(ctx, run, OSPREY_TABLE_PREFIX_ACCESS,
                            OSPREY_TABLE_ACCESS, sample_from);
    }
    /* Base facts. */
    {
        guint sample_from = ctx->base_facts->len;
        merge_base_family(ctx, run, OSPREY_TABLE_BASE, -1, sample_from);
        merge_base_family(ctx, run, OSPREY_TABLE_PREFIX_BASE,
                          OSPREY_TABLE_BASE, sample_from);
    }
    /* Copy facts. */
    {
        guint sample_from = ctx->copy_facts->len;
        merge_copy_facts(ctx, run, OSPREY_TABLE_COPY, -1, sample_from);
        merge_copy_facts(ctx, run, OSPREY_TABLE_PREFIX_COPY,
                         OSPREY_TABLE_COPY, sample_from);
    }
    /* Points-to facts. */
    {
        guint sample_from = ctx->points_facts->len;
        merge_points_facts(ctx, run, OSPREY_TABLE_POINTS, -1, sample_from);
        merge_points_facts(ctx, run, OSPREY_TABLE_PREFIX_POINTS,
                           OSPREY_TABLE_POINTS, sample_from);
    }
    /* Allocation facts. */
    {
        guint sample_from = ctx->alloc_facts->len;
        merge_alloc_facts(ctx, run, OSPREY_TABLE_ALLOC, -1, sample_from);
        merge_alloc_facts(ctx, run, OSPREY_TABLE_PREFIX_ALLOC,
                          OSPREY_TABLE_ALLOC, sample_from);
    }
    /* MayArray facts. */
    {
        guint sample_from = ctx->mayarray_facts->len;
        merge_mayarray_facts(ctx, run, OSPREY_TABLE_MAYARR, -1, sample_from);
        merge_mayarray_facts(ctx, run, OSPREY_TABLE_PREFIX_MAYARR,
                             OSPREY_TABLE_MAYARR, sample_from);
    }
    /* Region instances (bounds merge always; support once per sample). */
    {
        guint sample_from = ctx->region_instances->len;
        merge_region_instances(ctx, run, OSPREY_TABLE_REGION, -1,
                               sample_from);
        merge_region_instances(ctx, run, OSPREY_TABLE_PREFIX_REGION,
                               OSPREY_TABLE_REGION, sample_from);
    }

    merge_logical_accesses(ctx, sample_logical_accesses);
    g_array_free(sample_logical_accesses, TRUE);
    if (ctx->relations != NULL) {
        osprey_relations_free(ctx->relations);
        ctx->relations = NULL;
    }

    ctx->total_samples = sat_add_u64(ctx->total_samples, 1);
    /* The sample's dynamic observation total is the union of the frozen
     * prefix and the child suffix (child suffix counts are reset to 0
     * by prepare; the prefix count is preserved). */
    ctx->total_dynamic_observations = sat_add_u64(
        ctx->total_dynamic_observations,
        sat_add_u64(run->total_dynamic_prefix, run->total_dynamic_observations));

    log_msg("[osprey] [facts] [samples %llu] [access %u] [base %u] "
            "[copy %u] [points %u] [alloc %u] [may-array %u] "
            "[regions %u] [dynamic %llu]\n",
            (unsigned long long)ctx->total_samples,
            ctx->access_facts->len, ctx->base_facts->len,
            ctx->copy_facts->len, ctx->points_facts->len,
            ctx->alloc_facts->len, ctx->mayarray_facts->len,
            ctx->region_instances->len,
            (unsigned long long)ctx->total_dynamic_observations);

    /* Canonical dump: written after every successful merge so a harness
     * can compare runs byte-identically (ASLR invariance). */
    if (ctx->config.dump_file[0] != '\0') {
        osprey_dump_canonical(ctx, ctx->config.dump_file);
    }
    return OSPREY_OK;
}

/* ------------------------------------------------------------------ */
/* Canonical fact dump                                                 */
/* ------------------------------------------------------------------ */

/* Deterministic, sorted, full-key canonical dump.  Every line is a
 * stable function of the merged facts only: no raw addresses, no
 * pointer values, no hash iteration order.  Used by the t01_regions
 * harness to assert byte-identical output across ASLR/PIE runs. */
/* Canonical alloc rows sort by every printed field: site, requested
 * size, support. */
static gint osprey_alloc_dump_cmp(gconstpointer ap, gconstpointer bp) {
    const OspreyMallocFact *a = ap;
    const OspreyMallocFact *b = bp;
#define CMP(_field) do { \
        uint64_t av = (uint64_t)(a->_field); \
        uint64_t bv = (uint64_t)(b->_field); \
        if (av != bv) return av < bv ? -1 : 1; \
    } while (0)
    CMP(site_pc);
    CMP(requested_size);
    CMP(sample_support);
#undef CMP
    return 0;
}

/* Canonical may-array rows sort by every printed field in schema
 * order.  Signed offsets compare by their printed two's-complement
 * uint64_t representation, matching base/copy/points behavior. */
static gint osprey_mayarray_dump_cmp(gconstpointer ap, gconstpointer bp) {
    const OspreyMayArrayFact *a = ap;
    const OspreyMayArrayFact *b = bp;
#define CMP(_field) do { \
        uint64_t av = (uint64_t)(a->_field); \
        uint64_t bv = (uint64_t)(b->_field); \
        if (av != bv) return av < bv ? -1 : 1; \
    } while (0)
    CMP(start.region.kind);
    CMP(start.region.site_offset);
    CMP(start.offset);
    CMP(element_count);
    CMP(element_size);
    CMP(evidence_kind);
    CMP(sample_support);
#undef CMP
    return 0;
}

void osprey_dump_canonical(OspreyContext *ctx, const char *path) {
    if (ctx == NULL || path == NULL) return;
    FILE *f = fopen(path, "w");
    if (f == NULL) return;

    /* Region instances: sorted by canonical identity and creation
     * ordinal.  Raw addresses are represented only by an equivalence-
     * class ordinal, preserving reuse relationships without leaking
     * ASLR-dependent values into the canonical dump. */
    {
        GArray *rows = g_array_new(FALSE, FALSE, sizeof(OspreyRegionInstance));
        for (guint i = 0; i < ctx->region_instances->len; i++) {
            OspreyRegionInstance *r = &g_array_index(
                ctx->region_instances, OspreyRegionInstance, i);
            g_array_append_val(rows, *r);
        }
        for (guint i = 1; i < rows->len; i++) {
            OspreyRegionInstance key = g_array_index(rows,
                                                     OspreyRegionInstance, i);
            guint j = i;
            while (j > 0) {
                OspreyRegionInstance *prev = &g_array_index(
                    rows, OspreyRegionInstance, j - 1);
                if (prev->region.kind < key.region.kind ||
                    (prev->region.kind == key.region.kind &&
                     prev->region.site_offset < key.region.site_offset) ||
                    (prev->region.kind == key.region.kind &&
                     prev->region.site_offset == key.region.site_offset &&
                     prev->instance_id < key.instance_id)) {
                    break;
                }
                g_array_index(rows, OspreyRegionInstance, j) = *prev;
                j--;
            }
            g_array_index(rows, OspreyRegionInstance, j) = key;
        }
        for (guint i = 0; i < rows->len; i++) {
            OspreyRegionInstance *r = &g_array_index(rows,
                                                     OspreyRegionInstance, i);
            guint raw_class = i + 1;
            for (guint j = 0; j < i; j++) {
                OspreyRegionInstance *prev = &g_array_index(
                    rows, OspreyRegionInstance, j);
                if (prev->raw_base == r->raw_base) {
                    raw_class = j + 1;
                    break;
                }
            }
            fprintf(f, "region %u %llx %llu %u %llx\n",
                    (unsigned)r->region.kind,
                    (unsigned long long)r->region.site_offset,
                    (unsigned long long)r->instance_id,
                    raw_class,
                    (unsigned long long)(r->raw_max - r->raw_min));
        }
        g_array_free(rows, TRUE);
    }

    /* Access facts: sorted by (pc, is_store, region, offset, size). */
    {
        GArray *rows = g_array_new(FALSE, FALSE, sizeof(OspreyAccessFact));
        for (guint i = 0; i < ctx->access_facts->len; i++) {
            OspreyAccessFact *a = &g_array_index(ctx->access_facts,
                                                 OspreyAccessFact, i);
            g_array_append_val(rows, *a);
        }
        for (guint i = 1; i < rows->len; i++) {
            OspreyAccessFact key = g_array_index(rows, OspreyAccessFact, i);
            guint j = i;
            while (j > 0) {
                OspreyAccessFact *prev = &g_array_index(rows,
                                                        OspreyAccessFact, j - 1);
                if (access_fact_before(prev, &key)) {
                    break;
                }
                g_array_index(rows, OspreyAccessFact, j) = *prev;
                j--;
            }
            g_array_index(rows, OspreyAccessFact, j) = key;
        }
        for (guint i = 0; i < rows->len; i++) {
            OspreyAccessFact *a = &g_array_index(rows, OspreyAccessFact, i);
            if (a->op_class == 0) {
                /* Keep the canonical integer-row format byte-compatible
                 * with the accepted Stage-1 dump.  Non-integer rows carry
                 * the new trailing class field below. */
                fprintf(f, "access %llx %u %u %llx %llx %llu %u\n",
                        (unsigned long long)a->pc, (unsigned)a->is_store,
                        (unsigned)a->chunk.address.region.kind,
                        (unsigned long long)a->chunk.address.region.site_offset,
                        (unsigned long long)a->chunk.address.offset,
                        (unsigned long long)a->chunk.size,
                        (unsigned)a->sample_support);
            } else {
                fprintf(f, "access %llx %u %u %llx %llx %llu %u %u\n",
                        (unsigned long long)a->pc, (unsigned)a->is_store,
                        (unsigned)a->chunk.address.region.kind,
                        (unsigned long long)a->chunk.address.region.site_offset,
                        (unsigned long long)a->chunk.address.offset,
                        (unsigned long long)a->chunk.size,
                        (unsigned)a->sample_support, (unsigned)a->op_class);
            }
        }
        g_array_free(rows, TRUE);
    }

    /* Base facts: sorted by every printed field in order via a
     * dedicated comparator (never hash/insertion order):
     * access-pc, chunk kind, chunk site, chunk offset, chunk size,
     * base kind, base site, base offset, prov id, generation,
     * producer pc, support. */
    {
        GArray *rows = g_array_new(FALSE, FALSE, sizeof(OspreyBaseFact));
        for (guint i = 0; i < ctx->base_facts->len; i++) {
            OspreyBaseFact *b = &g_array_index(ctx->base_facts,
                                               OspreyBaseFact, i);
            g_array_append_val(rows, *b);
        }
        g_array_sort(rows, osprey_base_dump_cmp);
        for (guint i = 0; i < rows->len; i++) {
            OspreyBaseFact *b = &g_array_index(rows, OspreyBaseFact, i);
            fprintf(f,
                    "base %llx %u %llx %llx %llu %u %llx %llx %llu %u %llx %u\n",
                    (unsigned long long)b->pc,
                    (unsigned)b->chunk.address.region.kind,
                    (unsigned long long)b->chunk.address.region.site_offset,
                    (unsigned long long)b->chunk.address.offset,
                    (unsigned long long)b->chunk.size,
                    (unsigned)b->base.region.kind,
                    (unsigned long long)b->base.region.site_offset,
                    (unsigned long long)b->base.offset,
                    (unsigned long long)b->prov_object_id,
                    (unsigned)b->prov_generation,
                    (unsigned long long)b->producer_pc,
                    (unsigned)b->sample_support);
        }
        g_array_free(rows, TRUE);
    }

    /* Copy facts: sorted by every printed field
     * (src kind, src site, src offset, src size, dst kind, dst site,
     * dst offset, dst size, support). */
    {
        GArray *rows = g_array_new(FALSE, FALSE, sizeof(OspreyCopyFact));
        for (guint i = 0; i < ctx->copy_facts->len; i++) {
            OspreyCopyFact *c = &g_array_index(ctx->copy_facts,
                                               OspreyCopyFact, i);
            g_array_append_val(rows, *c);
        }
        g_array_sort(rows, osprey_copy_dump_cmp);
        for (guint i = 0; i < rows->len; i++) {
            OspreyCopyFact *c = &g_array_index(rows, OspreyCopyFact, i);
            fprintf(f,
                    "copy %u %llx %llx %llu %u %llx %llx %llu %u\n",
                    (unsigned)c->source.address.region.kind,
                    (unsigned long long)c->source.address.region.site_offset,
                    (unsigned long long)c->source.address.offset,
                    (unsigned long long)c->source.size,
                    (unsigned)c->destination.address.region.kind,
                    (unsigned long long)c->destination.address.region.site_offset,
                    (unsigned long long)c->destination.address.offset,
                    (unsigned long long)c->destination.size,
                    (unsigned)c->sample_support);
        }
        g_array_free(rows, TRUE);
    }

    /* Points-to facts: sorted by every printed field
     * (cell kind, cell site, cell offset, cell size, target kind,
     * target site, target offset, support, weak-numeric). */
    {
        GArray *rows = g_array_new(FALSE, FALSE, sizeof(OspreyPointsToFact));
        for (guint i = 0; i < ctx->points_facts->len; i++) {
            OspreyPointsToFact *p = &g_array_index(ctx->points_facts,
                                                   OspreyPointsToFact, i);
            g_array_append_val(rows, *p);
        }
        g_array_sort(rows, osprey_points_dump_cmp);
        for (guint i = 0; i < rows->len; i++) {
            OspreyPointsToFact *p = &g_array_index(rows,
                                                   OspreyPointsToFact, i);
            fprintf(f,
                    "points %u %llx %llx %llu %u %llx %llx %u %u\n",
                    (unsigned)p->pointer_chunk.address.region.kind,
                    (unsigned long long)p->pointer_chunk.address.region.site_offset,
                    (unsigned long long)p->pointer_chunk.address.offset,
                    (unsigned long long)p->pointer_chunk.size,
                    (unsigned)p->target.region.kind,
                    (unsigned long long)p->target.region.site_offset,
                    (unsigned long long)p->target.offset,
                    (unsigned)p->sample_support,
                    (unsigned)p->weak_numeric_evidence);
        }
        g_array_free(rows, TRUE);
    }

    /* Alloc facts: sorted by every printed field (site, requested
     * size, support).  Successful requested sizes only; failed calls
     * are diagnostics, never facts. */
    {
        GArray *rows = g_array_new(FALSE, FALSE, sizeof(OspreyMallocFact));
        for (guint i = 0; i < ctx->alloc_facts->len; i++) {
            OspreyMallocFact *a = &g_array_index(ctx->alloc_facts,
                                                 OspreyMallocFact, i);
            g_array_append_val(rows, *a);
        }
        g_array_sort(rows, osprey_alloc_dump_cmp);
        for (guint i = 0; i < rows->len; i++) {
            OspreyMallocFact *a = &g_array_index(rows, OspreyMallocFact, i);
            fprintf(f, "alloc %llx %llu %u\n",
                    (unsigned long long)a->site_pc,
                    (unsigned long long)a->requested_size,
                    (unsigned)a->sample_support);
        }
        g_array_free(rows, TRUE);
    }

    /* May-array facts: sorted by every printed field in schema order
     * (start kind, start site, start offset, element count, element
     * size, evidence kind, support). */
    {
        GArray *rows = g_array_new(FALSE, FALSE, sizeof(OspreyMayArrayFact));
        for (guint i = 0; i < ctx->mayarray_facts->len; i++) {
            OspreyMayArrayFact *m = &g_array_index(ctx->mayarray_facts,
                                                   OspreyMayArrayFact, i);
            g_array_append_val(rows, *m);
        }
        g_array_sort(rows, osprey_mayarray_dump_cmp);
        for (guint i = 0; i < rows->len; i++) {
            OspreyMayArrayFact *m = &g_array_index(rows, OspreyMayArrayFact,
                                                   i);
            fprintf(f,
                    "may-array %u %llx %llx %llu %llu %u %u\n",
                    (unsigned)m->start.region.kind,
                    (unsigned long long)m->start.region.site_offset,
                    (unsigned long long)(uint64_t)m->start.offset,
                    (unsigned long long)m->element_count,
                    (unsigned long long)m->element_size,
                    (unsigned)m->evidence_kind,
                    (unsigned)m->sample_support);
        }
        g_array_free(rows, TRUE);
    }

    fclose(f);
}

/* Analyze entry: Stage 3 deterministic construction, then (later stages)
 * inference and decoding. */
OspreyStatus osprey_analyze(OspreyContext *ctx) {
    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    /* Fail-closed transaction: every stage builds staged state; only a
     * fully OSPREY_OK transaction installs the graph/model.  Any
     * non-OK status rejects the transaction and leaves no model
     * exposed (Stage 0). */
    if (!osprey_tx_ok(ctx)) return osprey_tx_status(ctx);
    ctx->tx_model_ready = false;

    /* Stage 3.1 is independent of predicate/factor construction.  Build
     * its immutable parent-local relations first so later rule stages do
     * not rescan class-specific F01 rows. */
    OspreyStatus relation_status = osprey_relations_build(ctx);
    if (relation_status != OSPREY_OK) {
        osprey_tx_reject(ctx, relation_status, "relations",
                         "deterministic relation construction failed");
        return relation_status;
    }

    /* Fresh graph per transaction, built off to the side.  The
     * committed graph is replaced only on success. */
    OspreyGraph *old_graph = ctx->graph;
    ctx->staged_graph = osprey_graph_new();
    ctx->graph = ctx->staged_graph;

    OspreyStatus st = osprey_stage3_base(ctx);
    if (st != OSPREY_OK && st != OSPREY_DISABLED) {
        osprey_tx_reject(ctx, st, "closure", "stage-3 base construction failed");
        goto fail;
    }
    /* Stage 3a: secondary deterministic rules (CB02-CB09, CC04/CC05,
     * CD07/CD08); CC07 folding happens after the first BP pass. */
    st = osprey_stage3_secondary(ctx);
    if (st != OSPREY_OK && st != OSPREY_DISABLED) {
        osprey_tx_reject(ctx, st, "secondary",
                         "stage-3 secondary construction failed");
        goto fail;
    }
    /* Stage 3b: exact component solving + loopy BP + CC07 folding. */
    st = osprey_infer(ctx);
    if (st != OSPREY_OK && st != OSPREY_DISABLED) {
        osprey_tx_reject(ctx, st, "infer",
                         st == OSPREY_NON_CONVERGED
                             ? "belief propagation did not converge"
                         : st == OSPREY_EXACT_COMPONENT_TOO_LARGE
                             ? "exact component exceeds configured limit"
                             : "inference failed");
        goto fail;
    }
    /* Stage 4: consistent decoding into the OspreyModel. */
    st = osprey_decode(ctx);
    if (st != OSPREY_OK && st != OSPREY_DISABLED) {
        osprey_tx_reject(ctx, st, "decode", "decoder rejected model");
        goto fail;
    }

    /* Success: swap in the staged graph and model.  Detach the staged
     * graph first so tx_install frees the old committed graph, not the
     * staged one (ctx->graph aliased staged_graph during the build). */
    ctx->graph = old_graph;
    if (ctx->staged_graph == NULL || ctx->staged_model == NULL) {
        osprey_tx_reject(ctx, OSPREY_INVALID_MODEL, "install",
                         "missing staged graph or model");
        st = OSPREY_INVALID_MODEL;
        goto fail;
    }
    osprey_tx_install(ctx);
    log_msg("[osprey] [done] [status %d] [stages relations+base+secondary+infer+decode]\n",
            (int)st);
    return st;

fail:
    /* Detach the staged graph, then abort (frees staged graph/model). */
    ctx->graph = old_graph;
    osprey_tx_abort(ctx);
    return st;
}

const OspreyModel *osprey_model(const OspreyContext *ctx) {
    /* Fail-closed: consumers see a model only when the committed
     * transaction is OSPREY_OK. */
    if (ctx == NULL || ctx->tx_status != OSPREY_OK ||
        !ctx->tx_model_ready) return NULL;
    return ctx->model;
}
