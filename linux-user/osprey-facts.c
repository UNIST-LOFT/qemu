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
#include "provenance.h"
/* Helper entry points (DEF_HELPER in target/i386/helper.h).  helper-proto.h
 * cannot be included here (it pulls in target-specific helper.h); declare
 * the prototypes manually to satisfy -Werror=missing-prototypes.  These are
 * also visible to translate.c via the generated helper-proto.h. */
void helper_osprey_invalidate_reg(CPUArchState *env, uint32_t reg_idx);
void helper_osprey_reg_copy(CPUArchState *env, uint32_t dst_idx,
                            uint32_t src_idx, target_ulong src_val,
                            target_ulong dst_val);
void helper_osprey_reg_lea(CPUArchState *env, uint32_t dst_idx,
                           uint32_t base_idx, target_ulong disp,
                           target_ulong dst_val, target_ulong base_val);
void helper_osprey_set_ea(CPUArchState *env, uint32_t packed, uint32_t disp,
                          target_ulong base_val, target_ulong index_val);
void helper_osprey_mem_access(CPUArchState *env, target_ulong addr,
                              target_ulong size, target_ulong pc,
                              uint32_t is_store);
void helper_osprey_mem_copy(CPUArchState *env, target_ulong src,
                            target_ulong dst, target_ulong size);
void helper_osprey_on_load(CPUArchState *env, uint32_t dst_reg,
                           target_ulong addr, target_ulong size);
void helper_osprey_on_store(CPUArchState *env, uint32_t src_reg,
                            target_ulong addr, target_ulong size,
                            target_ulong src_val);
void helper_osprey_call(CPUArchState *env, target_ulong callee_pc,
                        target_ulong entry_sp);
void helper_osprey_ret(CPUArchState *env, target_ulong pc,
                       target_ulong sp);
void helper_osprey_rsp_update(CPUArchState *env, target_ulong new_sp,
                               target_ulong pc);

/* Origin shadow register invalidation (defined below; used by the
 * stack hooks above). */
static void origin_invalidate_reg(CPUArchState *env, int reg);

/* F04 points-to emission (defined below; called from the origin-shadow
 * spill/reload hooks). */
static void record_points_to(CPUArchState *env, target_ulong addr,
                             uint64_t size, target_ulong value,
                             uint64_t prov_object_id,
                             uint32_t prov_generation);

#include "qemu/thread.h"
#include "snapshot.h"

#include <stdlib.h>
#include <string.h>

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

uint64_t osprey_access_hash(const OspreyAccessFact *f) {
    OspreyKey k = osprey_chunk_key(&f->chunk);
    k.tag = 0x414343ULL; /* "ACC" */
    k.w[3] = f->pc;
    k.w[4] = f->is_store;
    return osprey_key_hash(&k);
}
bool osprey_access_eq(const OspreyAccessFact *a, const OspreyAccessFact *b) {
    return a->pc == b->pc && a->is_store == b->is_store &&
           eq_chunk(&a->chunk, &b->chunk);
}

uint64_t osprey_base_hash(const OspreyBaseFact *f) {
    OspreyKey k = osprey_chunk_key(&f->chunk);
    k.tag = 0x425345ULL; /* "BSE" */
    k.w[3] = f->pc;
    k.w[4] = (uint64_t)f->base.offset;
    k.w[5] = (uint64_t)f->base.region.kind;
    k.w[6] = f->base.region.site_offset;
    k.w[7] = f->prov_object_id;
    return osprey_key_hash(&k);
}
bool osprey_base_eq(const OspreyBaseFact *a, const OspreyBaseFact *b) {
    return a->pc == b->pc && eq_chunk(&a->chunk, &b->chunk) &&
           eq_addr(&a->base, &b->base) &&
           a->prov_object_id == b->prov_object_id &&
           a->prov_generation == b->prov_generation;
}

uint64_t osprey_copy_hash(const OspreyCopyFact *f) {
    OspreyKey k = osprey_chunk_key(&f->source);
    k.tag = 0x435059ULL; /* "CPY" */
    k.w[3] = (uint64_t)f->destination.address.offset;
    k.w[4] = f->destination.size;
    k.w[5] = (uint64_t)f->destination.address.region.kind;
    k.w[6] = f->destination.address.region.site_offset;
    return osprey_key_hash(&k);
}
bool osprey_copy_eq(const OspreyCopyFact *a, const OspreyCopyFact *b) {
    return eq_chunk(&a->source, &b->source) &&
           eq_chunk(&a->destination, &b->destination);
}

uint64_t osprey_points_hash(const OspreyPointsToFact *f) {
    OspreyKey k = osprey_chunk_key(&f->pointer_chunk);
    k.tag = 0x504E54ULL; /* "PNT" */
    k.w[3] = (uint64_t)f->target.offset;
    k.w[4] = (uint64_t)f->target.region.kind;
    k.w[5] = f->target.region.site_offset;
    return osprey_key_hash(&k);
}
bool osprey_points_eq(const OspreyPointsToFact *a, const OspreyPointsToFact *b) {
    return eq_chunk(&a->pointer_chunk, &b->pointer_chunk) &&
           eq_addr(&a->target, &b->target);
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
typedef void (*UpdateFn)(void *dst, const void *src);

/* Per-record updaters (support merge on duplicate). */
static void update_access_fact(void *dst, const void *src) {
    OspreyAccessFact *d = dst;
    const OspreyAccessFact *s = src;
    d->dynamic_count += s->dynamic_count;
    d->sample_support += s->sample_support;
}
static void update_base_fact(void *dst, const void *src) {
    OspreyBaseFact *d = dst;
    const OspreyBaseFact *s = src;
    d->sample_support += s->sample_support;
}
static void update_copy_fact(void *dst, const void *src) {
    OspreyCopyFact *d = dst;
    const OspreyCopyFact *s = src;
    d->sample_support += s->sample_support;
}
static void update_points_fact(void *dst, const void *src) {
    OspreyPointsToFact *d = dst;
    const OspreyPointsToFact *s = src;
    d->sample_support += s->sample_support;
    d->weak_numeric_evidence += s->weak_numeric_evidence;
}
static void update_malloc_fact(void *dst, const void *src) {
    OspreyMallocFact *d = dst;
    const OspreyMallocFact *s = src;
    d->sample_support += s->sample_support;
}
static void update_mayarray_fact(void *dst, const void *src) {
    OspreyMayArrayFact *d = dst;
    const OspreyMayArrayFact *s = src;
    d->sample_support += s->sample_support;
}

static uint32_t *table_used_ptr(OspreySharedRun *run, int table) {
    switch (table) {
    case OSPREY_TABLE_ACCESS: return &run->access_used;
    case OSPREY_TABLE_BASE: return &run->base_used;
    case OSPREY_TABLE_COPY: return &run->copy_used;
    case OSPREY_TABLE_POINTS: return &run->points_used;
    case OSPREY_TABLE_ALLOC: return &run->alloc_used;
    case OSPREY_TABLE_MAYARR: return &run->mayarray_used;
    default: return &run->region_used;
    }
}

static uint32_t table_cap_of(const OspreySharedRun *run, int table) {
    switch (table) {
    case OSPREY_TABLE_ACCESS: return run->access_cap;
    case OSPREY_TABLE_BASE: return run->base_cap;
    case OSPREY_TABLE_COPY: return run->copy_cap;
    case OSPREY_TABLE_POINTS: return run->points_cap;
    case OSPREY_TABLE_ALLOC: return run->alloc_cap;
    case OSPREY_TABLE_MAYARR: return run->mayarray_cap;
    default: return run->region_cap;
    }
}

static size_t table_record_size_of(int table) {
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

/* Generic insert; return 1 new, 0 duplicate-updated, -1 table full. */
static int run_table_insert(OspreySharedRun *run, int table, const void *rec,
                            HashFn hash, VerifyFn eq, UpdateFn upd) {
    uint32_t cap = table_cap_of(run, table);
    uint32_t used = *table_used_ptr(run, table);
    if (cap == 0 || used >= cap) {
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
            memcpy(ent, rec, rec_size);
            *table_used_ptr(run, table) = used + 1;
            return 1;
        }
        if (eq(ent, rec)) {
            if (upd != NULL) {
                upd(ent, rec);
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

int osprey_table_insert_access(OspreySharedRun *run, const OspreyAccessFact *f) {
    return run_table_insert(run, OSPREY_TABLE_ACCESS, f,
                            (HashFn)osprey_access_hash,
                            (VerifyFn)osprey_access_eq, update_access_fact);
}
int osprey_table_insert_base(OspreySharedRun *run, const OspreyBaseFact *f) {
    return run_table_insert(run, OSPREY_TABLE_BASE, f,
                            (HashFn)osprey_base_hash,
                            (VerifyFn)osprey_base_eq, update_base_fact);
}
int osprey_table_insert_copy(OspreySharedRun *run, const OspreyCopyFact *f) {
    return run_table_insert(run, OSPREY_TABLE_COPY, f,
                            (HashFn)osprey_copy_hash,
                            (VerifyFn)osprey_copy_eq, update_copy_fact);
}
int osprey_table_insert_points(OspreySharedRun *run, const OspreyPointsToFact *f) {
    return run_table_insert(run, OSPREY_TABLE_POINTS, f,
                            (HashFn)osprey_points_hash,
                            (VerifyFn)osprey_points_eq, update_points_fact);
}
int osprey_table_insert_alloc(OspreySharedRun *run, const OspreyMallocFact *f) {
    return run_table_insert(run, OSPREY_TABLE_ALLOC, f,
                            (HashFn)osprey_alloc_hash,
                            (VerifyFn)osprey_alloc_eq, update_malloc_fact);
}
int osprey_table_insert_mayarray(OspreySharedRun *run, const OspreyMayArrayFact *f) {
    return run_table_insert(run, OSPREY_TABLE_MAYARR, f,
                            (HashFn)osprey_mayarray_hash,
                            (VerifyFn)osprey_mayarray_eq, update_mayarray_fact);
}
/* Duplicate region instances merge observed bounds (min of raw_min, max
 * of raw_max) so a growing frame updates its shared record in place. */
static void update_region_instance(void *dst, const void *src) {
    OspreyRegionInstance *d = dst;
    const OspreyRegionInstance *s = src;
    d->sample_support += s->sample_support;
    if (s->raw_min < d->raw_min) d->raw_min = s->raw_min;
    if (s->raw_max > d->raw_max) d->raw_max = s->raw_max;
}
int osprey_table_insert_region(OspreySharedRun *run,
                               const OspreyRegionInstance *f) {
    return run_table_insert(run, OSPREY_TABLE_REGION, f,
                            (HashFn)osprey_region_instance_hash,
                            (VerifyFn)osprey_region_instance_eq,
                            update_region_instance);
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
 * never guesses a region from numeric proximity. */
bool osprey_region_of_addr(CPUArchState *env, target_ulong addr,
                           OspreyRegionId *region, int64_t *offset,
                           bool create) {
    (void)env;
    (void)create;
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
    OspreyRegOrigin *o = &st->regs[R_ESP];
    memset(o, 0, sizeof(*o));
    o->kind = OSPREY_ORIGIN_ADDRESS;
    o->valid = 1;
    o->concrete_value = sp;
    o->address.region = frame->region;
    o->address.offset = (int64_t)sp - (int64_t)frame->entry_sp;
    o->producer_pc = 0; /* synthetic: frame identity, not an insn */
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
    /* A RET always ends the current activation, even when a malformed
     * epilogue leaves the post-pop SP inside its old frame.  Pop that
     * frame first, then discard any additional stale frames whose exact
     * observed bounds cannot contain the surviving SP. */
    g_array_set_size(g_stack_frames, g_stack_frames->len - 1);
    while (g_stack_frames->len > 0) {
        OspreyStackFrame *top = &g_array_index(g_stack_frames,
                                               OspreyStackFrame,
                                               g_stack_frames->len - 1);
        if (sp >= top->min_sp && sp <= top->entry_sp) {
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
         * and grows its observed bound; there is no synthetic depth cap. */
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
                stack_seed_rsp_origin(env, f, new_sp);
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
    st->regs[reg].valid = 0;
    st->regs[reg].kind = OSPREY_ORIGIN_NONE;
}

static void origin_store_mem(CPUArchState *env, target_ulong addr,
                             target_ulong size, const OspreyRegOrigin *src) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    if (st->mem_slots == NULL) return;
    if (size != OSPREY_SHADOW_ALIGN || (addr & (OSPREY_SHADOW_ALIGN - 1))) {
        return; /* unsupported store: no metadata maintained */
    }
    OspreyMemSlotOrigin *slot = g_new0(OspreyMemSlotOrigin, 1);
    if (src->valid) {
        slot->valid = 1;
        slot->kind = src->kind;
        slot->chunk = src->chunk;
        slot->address = src->address;
        slot->concrete_value = src->concrete_value;
        slot->prov_object_id = src->prov_object_id;
        slot->prov_generation = src->prov_generation;
    }
    g_hash_table_replace(st->mem_slots, GSIZE_TO_POINTER(addr), slot);
}

/* Returns true when an ADDRESS origin was restored (F04 load-side
 * points-to evidence). */
static bool origin_load_slot(CPUArchState *env, target_ulong addr,
                             int dst_reg, target_ulong value) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    OspreyRegOrigin *dst = &st->regs[dst_reg];
    dst->valid = 0;
    dst->kind = OSPREY_ORIGIN_NONE;
    if (st->mem_slots == NULL || dst_reg < 0) return false;
    OspreyMemSlotOrigin *slot = g_hash_table_lookup(
        st->mem_slots, GSIZE_TO_POINTER(addr));
    if (slot == NULL || !slot->valid) return false;
    if (slot->concrete_value != value) return false; /* value-consistency */
    dst->valid = 1;
    dst->kind = slot->kind;
    dst->chunk = slot->chunk;
    dst->address = slot->address;
    dst->concrete_value = value;
    dst->prov_object_id = slot->prov_object_id;
    dst->prov_generation = slot->prov_generation;
    return slot->kind == OSPREY_ORIGIN_ADDRESS;
}

/* Full-width register copy: transfer ADDRESS/VALUE origin with a
 * value-consistency check. */
static void origin_mov_reg(CPUArchState *env, int dst, int src,
                           target_ulong src_val, target_ulong dst_val) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    OspreyRegOrigin *s = &st->regs[src];
    if (!s->valid || s->concrete_value != src_val) {
        origin_invalidate_reg(env, dst);
        return;
    }
    st->regs[dst] = *s;
    st->regs[dst].concrete_value = dst_val;
}

/* lea dst, [base + disp]: propagate ADDRESS origin with offset += disp
 * when the arithmetic is exact (checked). */
static void origin_lea_imm(CPUArchState *env, int dst, int base,
                           int64_t disp, target_ulong dst_val,
                           target_ulong base_val) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    OspreyRegOrigin *b = &st->regs[base];
    if (!b->valid || b->kind != OSPREY_ORIGIN_ADDRESS ||
        b->concrete_value != base_val) {
        origin_invalidate_reg(env, dst);
        return;
    }
    int64_t off = 0;
    if (!osprey_check_add(b->address.offset, disp, &off)) {
        origin_invalidate_reg(env, dst);
        return;
    }
    st->regs[dst] = *b;
    st->regs[dst].address.offset = off;
    st->regs[dst].concrete_value = dst_val;
}

/* Runtime helpers exposed to the translator wrappers. */
void osprey_on_reg_copy(CPUArchState *env, uint32_t dst, uint32_t src,
                        target_ulong src_val, target_ulong dst_val) {
    origin_mov_reg(env, (int)dst, (int)src, src_val, dst_val);
}

void osprey_on_reg_lea(CPUArchState *env, uint32_t dst, uint32_t base,
                       int64_t disp, target_ulong dst_val,
                       target_ulong base_val) {
    origin_lea_imm(env, (int)dst, (int)base, disp, dst_val, base_val);
}

void osprey_on_reg_invalidate(CPUArchState *env, uint32_t reg) {
    origin_invalidate_reg(env, (int)reg);
}

/* Aligned native-width store of register origin into the memory shadow. */
void osprey_on_mem_store_origin(CPUArchState *env, uint32_t src_reg,
                                target_ulong addr, target_ulong size,
                                target_ulong src_val) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    OspreyRegOrigin *s = (src_reg < CPU_NB_REGS) ? &st->regs[src_reg] : NULL;
    OspreyRegOrigin tmp;
    memset(&tmp, 0, sizeof(tmp));
    if (s != NULL && s->valid && s->concrete_value == src_val) {
        tmp = *s;
        if (s->kind == OSPREY_ORIGIN_ADDRESS && size == OSPREY_SHADOW_ALIGN) {
            record_points_to(env, addr, size, src_val,
                             s->prov_object_id, s->prov_generation);
        }
    }
    origin_store_mem(env, addr, size, &tmp);
}

/* Aligned native-width load: restore the origin into dst_reg, guarded by
 * the value-consistency check. */
void osprey_on_mem_load_origin(CPUArchState *env, uint32_t dst_reg,
                               target_ulong addr, target_ulong value) {
    if (origin_load_slot(env, addr, (int)dst_reg, value)) {
        /* F04 load-side: a pointer-width slot holding an ADDRESS origin
         * is points-to evidence: the loaded value points at that
         * canonical address. */
        OspreyCpuOriginState *st = osprey_cpu_origin(env);
        OspreyRegOrigin *dst = &st->regs[dst_reg];
        record_points_to(env, addr, 8, value,
                         dst->prov_object_id, dst->prov_generation);
    }
}

/* Provenance-authoritative heap origin check: the origin's identity must
 * reference a LIVE object whose base matches the origin's concrete
 * value.  Used before F02/F04 emission for heap ADDRESS origins. */
bool osprey_origin_prov_live(const OspreyRegOrigin *o) {
    if (o->prov_object_id == 0) {
        return true; /* non-heap or legacy origin: numeric resolution */
    }
    ProvenanceObject *obj =
        provenance_lookup_object(o->prov_object_id, o->prov_generation);
    if (obj == NULL || obj->state != PROV_OBJ_LIVE) {
        return false;
    }
    /* The concrete value and canonical offset must identify the same
     * byte in the live object.  Subtraction after the lower-bound check
     * avoids base+size wraparound. */
    if (o->concrete_value < obj->base) {
        return false;
    }
    uint64_t delta = (uint64_t)(o->concrete_value - obj->base);
    if (delta >= obj->requested_size || delta > INT64_MAX ||
        o->address.offset != (int64_t)delta) {
        return false;
    }
    uint64_t site = 0;
    if (!osprey_normalize_pc(obj->alloc_pc, &site) ||
        o->address.region.kind != OSPREY_REGION_HEAP_SITE ||
        o->address.region.site_offset != site) {
        return false;
    }
    return true;
}

/* ------------------------------------------------------------------ */
/* Allocation instance tracking                                        */
/* ------------------------------------------------------------------ */

static OspreySharedRun *g_shared_run = NULL;
static QemuMutex g_shared_mutex;
static bool g_shared_mutex_init = false;

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

void osprey_on_alloc_success(CPUArchState *env, target_ulong base,
                             target_ulong size, target_ulong site_pc,
                             uint64_t object_id, uint32_t generation) {
    if (base == 0 && size != 0) return; /* failure: no object */
    uint64_t raw_base = (uint64_t)base;
    uint64_t raw_size = (uint64_t)size;
    if (raw_size > INT64_MAX || raw_base > UINT64_MAX - raw_size) {
        if (g_shared_run != NULL) {
            g_shared_run->bad_arithmetic = 1;
        }
        return;
    }
    uint64_t norm_pc = 0;
    if (!osprey_normalize_pc(site_pc, &norm_pc)) {
        /* Allocation from out-of-image code (libc-internal): the site
         * is not part of the main image; record nothing. */
        return;
    }
    ProvenanceObject *obj = provenance_lookup_object(object_id, generation);
    if (obj == NULL || obj->state != PROV_OBJ_LIVE || obj->base != base ||
        obj->requested_size != size || obj->alloc_pc != site_pc) {
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
    h.size = size;
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
        fact.requested_size = (int64_t)size;
        fact.sample_support = 1;
        qemu_mutex_lock(&g_shared_mutex);
        osprey_table_insert_alloc(run, &fact);
        qemu_mutex_unlock(&g_shared_mutex);
    }

    /* Seed the ADDRESS origin of the return register (RAX) so
     * subsequent loads/stores through the pointer emit F02 BaseAddr
     * facts instead of being opaque.  The origin is keyed to this heap
     * instance (offset 0, pointer width). */
    {
        OspreyCpuOriginState *st = osprey_cpu_origin(env);
        OspreyRegOrigin *o = &st->regs[R_EAX];
        memset(o, 0, sizeof(*o));
        o->kind = OSPREY_ORIGIN_ADDRESS;
        o->valid = 1;
        o->concrete_value = base;
        o->address.region = h.region;
        o->address.offset = 0;
        o->producer_pc = norm_pc;
        o->prov_object_id = object_id;
        o->prov_generation = generation;
    }

    /* F06 MayArray: the allocation-argument heuristic records the
     * requested element geometry when the site is a two-argument
     * calloc-style call.  Calloc is modeled with total size in the
     * pending op; the count/size split is not recoverable here, so the
     * fact records a single element of the requested size (kind 0). */
    if (run != NULL) {
        OspreyMayArrayFact mf;
        memset(&mf, 0, sizeof(mf));
        mf.start.region = h.region;
        mf.start.offset = 0;
        mf.element_count = 1;
        mf.element_size = (uint32_t)(size > 0xffffffffu
                                     ? 0xffffffffu : size);
        mf.evidence_kind = 1; /* direct allocation-size evidence */
        mf.sample_support = 1;
        qemu_mutex_lock(&g_shared_mutex);
        osprey_table_insert_mayarray(run, &mf);
        qemu_mutex_unlock(&g_shared_mutex);
    }
}

void osprey_on_alloc_failure(CPUArchState *env, target_ulong site_pc) {
    (void)env;
    uint64_t norm_pc = 0;
    if (!osprey_normalize_pc(site_pc, &norm_pc)) {
        return;
    }
    OspreySharedRun *run = g_shared_run;
    if (run != NULL) {
        OspreyMallocFact fact;
        memset(&fact, 0, sizeof(fact));
        fact.site_pc = norm_pc;
        fact.requested_size = -1; /* explicit failure state */
        fact.sample_support = 1;
        qemu_mutex_lock(&g_shared_mutex);
        osprey_table_insert_alloc(run, &fact);
        qemu_mutex_unlock(&g_shared_mutex);
    }
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
                               const OspreyChunk *chunk, int is_store) {
    if (run == NULL) return;
    OspreyAccessFact fact;
    memset(&fact, 0, sizeof(fact));
    fact.pc = pc;
    fact.chunk = *chunk;
    fact.dynamic_count = 1;
    fact.sample_support = 1;
    fact.is_store = (uint8_t)(is_store != 0);
    qemu_mutex_lock(&g_shared_mutex);
    osprey_table_insert_access(run, &fact);
    qemu_mutex_unlock(&g_shared_mutex);
    run->total_dynamic_observations++;
}

/* F04 PointsTo: a pointer-width slot holding an ADDRESS origin at
 * `addr` pointing to `value`.  Both the slot and the target must resolve
 * to canonical regions; a target outside every modeled region records
 * nothing (never guessed from proximity). */
static void record_points_to(CPUArchState *env, target_ulong addr,
                             uint64_t size, target_ulong value,
                             uint64_t prov_object_id,
                             uint32_t prov_generation) {
    OspreySharedRun *run = g_shared_run;
    if (run == NULL) return;
    OspreyRegionId preg, treg;
    int64_t poff, toff;
    if (!osprey_region_of_addr(env, addr, &preg, &poff, false)) {
        run->bad_region = 1;
        return;
    }
    /* Provenance-authoritative heap targets: the origin identity must
     * still reference a LIVE object whose base matches the concrete
     * value; a stale identity (freed/reused) records nothing. */
    if (prov_object_id != 0) {
        ProvenanceObject *obj =
            provenance_lookup_object(prov_object_id, prov_generation);
        if (obj == NULL || obj->state != PROV_OBJ_LIVE) {
            return;
        }
        /* The pointer value must lie inside the live object. */
        if (value < obj->base ||
            (uint64_t)(value - obj->base) >= obj->requested_size) {
            return;
        }
    }
    if (!osprey_region_of_addr(env, value, &treg, &toff, false)) {
        return; /* pointer target not in a modeled region */
    }
    OspreyPointsToFact fact;
    memset(&fact, 0, sizeof(fact));
    fact.pointer_chunk.address.region = preg;
    fact.pointer_chunk.address.offset = poff;
    fact.pointer_chunk.size = size;
    fact.target.region = treg;
    fact.target.offset = toff;
    fact.sample_support = 1;
    qemu_mutex_lock(&g_shared_mutex);
    osprey_table_insert_points(run, &fact);
    qemu_mutex_unlock(&g_shared_mutex);
}

void osprey_set_ea(CPUArchState *env, uint32_t packed, uint32_t disp,
                          target_ulong base_val, target_ulong index_val) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    st->ea_valid = (packed & 0x80000000u) != 0;
    st->ea_base_reg = (int32_t)((packed >> 16) & 0xff) - 1; /* -1 = none */
    st->ea_index_reg = (int32_t)((packed >> 8) & 0xff) - 1;
    st->ea_scale = (int32_t)(packed & 0xff);
    st->ea_disp = (int64_t)(int32_t)disp;
    st->ea_base_val = base_val;
    st->ea_index_val = index_val;
    /* Snapshot the base/index origins NOW: the registers may be killed
     * by the access itself before osprey_on_mem_access consumes the EA
     * (e.g. mov (%rax),%rax). */
    memset(&st->ea_base_origin, 0, sizeof(st->ea_base_origin));
    memset(&st->ea_index_origin, 0, sizeof(st->ea_index_origin));
    if (st->ea_base_reg >= 0 && st->ea_base_reg < CPU_NB_REGS) {
        st->ea_base_origin = st->regs[st->ea_base_reg];
    }
    if (st->ea_index_reg >= 0 && st->ea_index_reg < CPU_NB_REGS) {
        st->ea_index_origin = st->regs[st->ea_index_reg];
    }
}

void osprey_on_mem_access(CPUArchState *env, target_ulong addr,
                          uint64_t size, uint64_t pc, uint32_t is_store) {
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    OspreySharedRun *run = g_shared_run;
    if (run == NULL) return;

    /* Normalize the PC against the main image base; facts from
     * out-of-image code (libraries, interpreter) are not part of the
     * main-image model and are skipped entirely. */
    uint64_t norm_pc = 0;
    if (!osprey_normalize_pc(pc, &norm_pc)) {
        /* Consume (clear) the EA metadata even when skipping: a stale
         * record must never be misread by a later in-image access. */
        st->ea_valid = false;
        return;
    }
    pc = norm_pc;

    /* Consume the EA metadata: copy into locals, then clear so a stale
     * record can never be misread by a later instruction. */
    bool have_ea = st->ea_valid;
    int base_reg = st->ea_base_reg;
    int index_reg = st->ea_index_reg;
    int scale = st->ea_scale;
    int64_t disp = st->ea_disp;
    target_ulong base_val = st->ea_base_val;
    target_ulong index_val = st->ea_index_val;
    st->ea_valid = false;

    /* Resolve the accessed chunk to a canonical region.  Accesses that
     * do not resolve (libraries, anonymous mmap) are counted as bad
     * region events, never forced into a region. */
    OspreyRegionId region;
    int64_t off;
    if (osprey_region_of_addr(env, addr, &region, &off, false)) {
        OspreyChunk chunk;
        chunk.address.region = region;
        chunk.address.offset = off;
        chunk.size = size;

        record_access_fact(run, pc, &chunk, is_store != 0);

        /* F02 BaseAddr: emit only when the EA decomposition proves the
         * base relationship: the base register carries a valid ADDRESS
         * origin whose concrete value matches base_val.  Index-only
         * forms (scale == 1, no base) are equivalent. */
        if (have_ea && base_reg >= 0 && base_reg < CPU_NB_REGS) {
            OspreyRegOrigin *b = &st->ea_base_origin;
            if (b->valid && b->kind == OSPREY_ORIGIN_ADDRESS &&
                b->concrete_value == base_val) {
                /* Provenance-authoritative heap bases: the origin must
                 * still reference a LIVE object with a matching base;
                 * a stale identity (freed/reused) emits nothing. */
                bool prov_ok = true;
                if (b->address.region.kind == OSPREY_REGION_HEAP_SITE) {
                    prov_ok = osprey_origin_prov_live(b);
                }
                if (prov_ok) {
                    OspreyBaseFact bf;
                    memset(&bf, 0, sizeof(bf));
                    bf.pc = pc;
                    bf.chunk = chunk;
                    bf.base = b->address;
                    bf.prov_object_id = b->prov_object_id;
                    bf.prov_generation = b->prov_generation;
                    bf.sample_support = 1;
                    qemu_mutex_lock(&g_shared_mutex);
                    osprey_table_insert_base(run, &bf);
                    qemu_mutex_unlock(&g_shared_mutex);
                }
            }
        } else if (have_ea && index_reg >= 0 && index_reg < CPU_NB_REGS &&
                   scale == 1) {
            OspreyRegOrigin *ix = &st->ea_index_origin;
            if (ix->valid && ix->kind == OSPREY_ORIGIN_ADDRESS &&
                ix->concrete_value == index_val) {
                bool prov_ok = true;
                if (ix->address.region.kind == OSPREY_REGION_HEAP_SITE) {
                    prov_ok = osprey_origin_prov_live(ix);
                }
                if (prov_ok) {
                    OspreyBaseFact bf;
                    memset(&bf, 0, sizeof(bf));
                    bf.pc = pc;
                    bf.chunk = chunk;
                    bf.base = ix->address;
                    bf.prov_object_id = ix->prov_object_id;
                    bf.prov_generation = ix->prov_generation;
                    bf.sample_support = 1;
                    qemu_mutex_lock(&g_shared_mutex);
                    osprey_table_insert_base(run, &bf);
                    qemu_mutex_unlock(&g_shared_mutex);
                }
            }
        }
    } else {
        run->bad_region = 1;
    }

    /* F04 PointsTo: a pointer-width stored/loaded value carrying a valid
     * ADDRESS origin records canonical points-to.  The value-origin of
     * the data register is tracked by osprey_on_mem_store_origin; the
     * translator pairs that hook with this one at pointer-width sites. */
    (void)disp;
}

/* Modeled byte copies (memcpy/memmove/strcpy family).  Records F03 as
 * one exact chunk pair when the copy is pointer-sized and both ends
 * resolve; larger copies are represented as observed-width chunks only
 * (never expanded byte-by-byte). */
void osprey_on_mem_copy(CPUArchState *env, target_ulong src,
                        target_ulong dst, target_ulong size) {
    OspreySharedRun *run = g_shared_run;
    if (run == NULL) return;
    if (size == 0) return;
    OspreyRegionId sreg, dreg;
    int64_t soff, doff;
    if (!osprey_region_of_addr(env, src, &sreg, &soff, false)) {
        run->bad_region = 1;
        return;
    }
    if (!osprey_region_of_addr(env, dst, &dreg, &doff, false)) {
        run->bad_region = 1;
        return;
    }
    OspreyCopyFact fact;
    memset(&fact, 0, sizeof(fact));
    fact.source.address.region = sreg;
    fact.source.address.offset = soff;
    fact.source.size = size;
    fact.destination.address.region = dreg;
    fact.destination.address.offset = doff;
    fact.destination.size = size;
    fact.sample_support = 1;
    qemu_mutex_lock(&g_shared_mutex);
    osprey_table_insert_copy(run, &fact);
    qemu_mutex_unlock(&g_shared_mutex);
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

static bool osprey_run_population_valid(const OspreySharedRun *run) {
    static const int tables[] = {
        OSPREY_TABLE_ACCESS, OSPREY_TABLE_BASE, OSPREY_TABLE_COPY,
        OSPREY_TABLE_POINTS, OSPREY_TABLE_ALLOC, OSPREY_TABLE_MAYARR,
        OSPREY_TABLE_REGION,
    };
    const uint32_t used[] = {
        run->access_used, run->base_used, run->copy_used,
        run->points_used, run->alloc_used, run->mayarray_used,
        run->region_used,
    };
    for (size_t i = 0; i < G_N_ELEMENTS(tables); i++) {
        OspreyRunIter it;
        const void *record;
        uint32_t count = 0;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = tables[i];
        while (osprey_run_iter_next(&it, &record)) {
            count++;
        }
        if (count != used[i]) return false;
    }
    return true;
}

/* Merge one completed sample (patch-0/iter-1 child run) into the
 * committed parent tables.  Duplicates merge support in place; the
 * merged record keeps the union of sample support.  Returns
 * OSPREY_INCOMPLETE_FACTS when the sample overflowed (the model must
 * not be installed from incomplete facts). */
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
        run->region_used > run->region_cap) {
        osprey_tx_reject(ctx, OSPREY_INCOMPLETE_FACTS, "merge",
                         "used exceeds capacity");
        return OSPREY_INCOMPLETE_FACTS;
    }
    if (!osprey_run_population_valid(run)) {
        osprey_tx_reject(ctx, OSPREY_INCOMPLETE_FACTS, "merge",
                         "used count does not match table population");
        return OSPREY_INCOMPLETE_FACTS;
    }

    OspreyRunIter it;
    const void *rec;

    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = OSPREY_TABLE_ACCESS;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyAccessFact *f = rec;
        bool merged = false;
        for (guint i = 0; i < ctx->access_facts->len; i++) {
            OspreyAccessFact *d = &g_array_index(ctx->access_facts,
                                                 OspreyAccessFact, i);
            if (osprey_access_eq(d, f)) {
                d->dynamic_count += f->dynamic_count;
                d->sample_support += f->sample_support;
                merged = true;
                break;
            }
        }
        if (!merged) {
            g_array_append_val(ctx->access_facts, *f);
        }
    }

    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = OSPREY_TABLE_BASE;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyBaseFact *f = rec;
        bool merged = false;
        for (guint i = 0; i < ctx->base_facts->len; i++) {
            OspreyBaseFact *d = &g_array_index(ctx->base_facts,
                                               OspreyBaseFact, i);
            if (osprey_base_eq(d, f)) {
                d->sample_support += f->sample_support;
                merged = true;
                break;
            }
        }
        if (!merged) {
            g_array_append_val(ctx->base_facts, *f);
        }
    }

    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = OSPREY_TABLE_COPY;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyCopyFact *f = rec;
        bool merged = false;
        for (guint i = 0; i < ctx->copy_facts->len; i++) {
            OspreyCopyFact *d = &g_array_index(ctx->copy_facts,
                                               OspreyCopyFact, i);
            if (osprey_copy_eq(d, f)) {
                d->sample_support += f->sample_support;
                merged = true;
                break;
            }
        }
        if (!merged) {
            g_array_append_val(ctx->copy_facts, *f);
        }
    }

    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = OSPREY_TABLE_POINTS;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyPointsToFact *f = rec;
        bool merged = false;
        for (guint i = 0; i < ctx->points_facts->len; i++) {
            OspreyPointsToFact *d = &g_array_index(ctx->points_facts,
                                                   OspreyPointsToFact, i);
            if (osprey_points_eq(d, f)) {
                d->sample_support += f->sample_support;
                d->weak_numeric_evidence += f->weak_numeric_evidence;
                merged = true;
                break;
            }
        }
        if (!merged) {
            g_array_append_val(ctx->points_facts, *f);
        }
    }

    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = OSPREY_TABLE_ALLOC;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyMallocFact *f = rec;
        bool merged = false;
        for (guint i = 0; i < ctx->alloc_facts->len; i++) {
            OspreyMallocFact *d = &g_array_index(ctx->alloc_facts,
                                                 OspreyMallocFact, i);
            if (osprey_alloc_eq(d, f)) {
                d->sample_support += f->sample_support;
                merged = true;
                break;
            }
        }
        if (!merged) {
            g_array_append_val(ctx->alloc_facts, *f);
        }
    }

    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = OSPREY_TABLE_MAYARR;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyMayArrayFact *f = rec;
        bool merged = false;
        for (guint i = 0; i < ctx->mayarray_facts->len; i++) {
            OspreyMayArrayFact *g = &g_array_index(ctx->mayarray_facts,
                                                   OspreyMayArrayFact, i);
            if (osprey_mayarray_eq(g, f)) {
                g->sample_support += f->sample_support;
                merged = true;
                break;
            }
        }
        if (!merged) {
            g_array_append_val(ctx->mayarray_facts, *f);
        }
    }

    memset(&it, 0, sizeof(it));
    it.run = run;
    it.table = OSPREY_TABLE_REGION;
    while (osprey_run_iter_next(&it, &rec)) {
        const OspreyRegionInstance *f = rec;
        bool merged = false;
        for (guint i = 0; i < ctx->region_instances->len; i++) {
            OspreyRegionInstance *d = &g_array_index(ctx->region_instances,
                                                     OspreyRegionInstance, i);
            if (osprey_region_instance_eq(d, f)) {
                d->sample_support += f->sample_support;
                if (f->raw_min < d->raw_min) d->raw_min = f->raw_min;
                if (f->raw_max > d->raw_max) d->raw_max = f->raw_max;
                merged = true;
                break;
            }
        }
        if (!merged) {
            g_array_append_val(ctx->region_instances, *f);
        }
    }

    ctx->total_samples += 1;
    ctx->total_dynamic_observations += run->total_dynamic_observations;

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
                if (prev->pc < key.pc ||
                    (prev->pc == key.pc && prev->is_store < key.is_store) ||
                    (prev->pc == key.pc && prev->is_store == key.is_store &&
                     prev->chunk.address.region.kind <
                         key.chunk.address.region.kind) ||
                    (prev->pc == key.pc && prev->is_store == key.is_store &&
                     prev->chunk.address.region.kind ==
                         key.chunk.address.region.kind &&
                     prev->chunk.address.region.site_offset <
                         key.chunk.address.region.site_offset) ||
                    (prev->pc == key.pc && prev->is_store == key.is_store &&
                     prev->chunk.address.region.kind ==
                         key.chunk.address.region.kind &&
                     prev->chunk.address.region.site_offset ==
                         key.chunk.address.region.site_offset &&
                     prev->chunk.address.offset < key.chunk.address.offset) ||
                    (prev->pc == key.pc && prev->is_store == key.is_store &&
                     prev->chunk.address.region.kind ==
                         key.chunk.address.region.kind &&
                     prev->chunk.address.region.site_offset ==
                         key.chunk.address.region.site_offset &&
                     prev->chunk.address.offset == key.chunk.address.offset &&
                     prev->chunk.size < key.chunk.size)) {
                    break;
                }
                g_array_index(rows, OspreyAccessFact, j) = *prev;
                j--;
            }
            g_array_index(rows, OspreyAccessFact, j) = key;
        }
        for (guint i = 0; i < rows->len; i++) {
            OspreyAccessFact *a = &g_array_index(rows, OspreyAccessFact, i);
            fprintf(f, "access %llx %u %u %llx %llx %llu %u\n",
                    (unsigned long long)a->pc, (unsigned)a->is_store,
                    (unsigned)a->chunk.address.region.kind,
                    (unsigned long long)a->chunk.address.region.site_offset,
                    (unsigned long long)a->chunk.address.offset,
                    (unsigned long long)a->chunk.size,
                    (unsigned)a->sample_support);
        }
        g_array_free(rows, TRUE);
    }

    /* Base facts: sorted by (pc, region, offset, prov id). */
    {
        GArray *rows = g_array_new(FALSE, FALSE, sizeof(OspreyBaseFact));
        for (guint i = 0; i < ctx->base_facts->len; i++) {
            OspreyBaseFact *b = &g_array_index(ctx->base_facts,
                                               OspreyBaseFact, i);
            g_array_append_val(rows, *b);
        }
        for (guint i = 1; i < rows->len; i++) {
            OspreyBaseFact key = g_array_index(rows, OspreyBaseFact, i);
            guint j = i;
            while (j > 0) {
                OspreyBaseFact *prev = &g_array_index(rows,
                                                      OspreyBaseFact, j - 1);
                if (prev->pc < key.pc ||
                    (prev->pc == key.pc &&
                     prev->base.region.kind < key.base.region.kind) ||
                    (prev->pc == key.pc &&
                     prev->base.region.kind == key.base.region.kind &&
                     prev->base.region.site_offset <
                         key.base.region.site_offset) ||
                    (prev->pc == key.pc &&
                     prev->base.region.kind == key.base.region.kind &&
                     prev->base.region.site_offset ==
                         key.base.region.site_offset &&
                     prev->base.offset < key.base.offset) ||
                    (prev->pc == key.pc &&
                     prev->base.region.kind == key.base.region.kind &&
                     prev->base.region.site_offset ==
                         key.base.region.site_offset &&
                     prev->base.offset == key.base.offset &&
                     prev->prov_object_id < key.prov_object_id)) {
                    break;
                }
                g_array_index(rows, OspreyBaseFact, j) = *prev;
                j--;
            }
            g_array_index(rows, OspreyBaseFact, j) = key;
        }
        for (guint i = 0; i < rows->len; i++) {
            OspreyBaseFact *b = &g_array_index(rows, OspreyBaseFact, i);
            fprintf(f, "base %llx %u %llx %llx %llx %u %u\n",
                    (unsigned long long)b->pc,
                    (unsigned)b->chunk.address.region.kind,
                    (unsigned long long)b->chunk.address.region.site_offset,
                    (unsigned long long)b->chunk.address.offset,
                    (unsigned long long)b->base.offset,
                    (unsigned)b->prov_object_id,
                    (unsigned)b->prov_generation);
        }
        g_array_free(rows, TRUE);
    }

    /* Alloc facts: sorted by (site_pc, requested_size). */
    {
        GArray *rows = g_array_new(FALSE, FALSE, sizeof(OspreyMallocFact));
        for (guint i = 0; i < ctx->alloc_facts->len; i++) {
            OspreyMallocFact *a = &g_array_index(ctx->alloc_facts,
                                                 OspreyMallocFact, i);
            g_array_append_val(rows, *a);
        }
        for (guint i = 1; i < rows->len; i++) {
            OspreyMallocFact key = g_array_index(rows, OspreyMallocFact, i);
            guint j = i;
            while (j > 0) {
                OspreyMallocFact *prev = &g_array_index(rows,
                                                        OspreyMallocFact, j - 1);
                if (prev->site_pc < key.site_pc ||
                    (prev->site_pc == key.site_pc &&
                     prev->requested_size < key.requested_size)) {
                    break;
                }
                g_array_index(rows, OspreyMallocFact, j) = *prev;
                j--;
            }
            g_array_index(rows, OspreyMallocFact, j) = key;
        }
        for (guint i = 0; i < rows->len; i++) {
            OspreyMallocFact *a = &g_array_index(rows, OspreyMallocFact, i);
            fprintf(f, "alloc %llx %lld %u\n",
                    (unsigned long long)a->site_pc,
                    (long long)a->requested_size,
                    (unsigned)a->sample_support);
        }
        g_array_free(rows, TRUE);
    }

    fclose(f);
}

/* Analyze entry: Stage 2 deterministic closure, then (later stages)
 * inference and decoding. */
OspreyStatus osprey_analyze(OspreyContext *ctx) {
    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    /* Fail-closed transaction: every stage builds staged state; only a
     * fully OSPREY_OK transaction installs the graph/model.  Any
     * non-OK status rejects the transaction and leaves no model
     * exposed (Stage 0). */
    if (!osprey_tx_ok(ctx)) return osprey_tx_status(ctx);
    ctx->tx_model_ready = false;

    /* Fresh graph per transaction, built off to the side.  The
     * committed graph is replaced only on success. */
    OspreyGraph *old_graph = ctx->graph;
    ctx->staged_graph = osprey_graph_new();
    ctx->graph = ctx->staged_graph;

    OspreyStatus st = osprey_stage2_closure(ctx);
    if (st != OSPREY_OK && st != OSPREY_DISABLED) {
        osprey_tx_reject(ctx, st, "closure", "stage-2 closure failed");
        goto fail;
    }
    /* Stage 3a: secondary deterministic rules (CB02-CB09, CC04/CC05,
     * CD07/CD08); CC07 folding happens after the first BP pass. */
    st = osprey_stage2_secondary(ctx);
    if (st != OSPREY_OK && st != OSPREY_DISABLED) {
        osprey_tx_reject(ctx, st, "secondary", "stage-2 secondary failed");
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
    log_msg("[osprey] [done] [status %d] [stages closure+secondary+infer+decode]\n",
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

void helper_osprey_invalidate_reg(CPUArchState *env, uint32_t i) {
    origin_invalidate_reg(env, (int)i);
}

void helper_osprey_reg_copy(CPUArchState *env, uint32_t dst, uint32_t src,
                            target_ulong src_val, target_ulong dst_val) {
    origin_mov_reg(env, (int)dst, (int)src, src_val, dst_val);
}

void helper_osprey_reg_lea(CPUArchState *env, uint32_t dst, uint32_t base,
                           target_ulong disp, target_ulong dst_val,
                           target_ulong base_val) {
    origin_lea_imm(env, (int)dst, (int)base, (int64_t)(int32_t)disp,
                   dst_val, base_val);
}

void helper_osprey_set_ea(CPUArchState *env, uint32_t packed, uint32_t disp,
                          target_ulong base_val, target_ulong index_val) {
    osprey_set_ea(env, packed, disp, base_val, index_val);
}

void helper_osprey_mem_access(CPUArchState *env, target_ulong addr,
                              target_ulong size, target_ulong pc,
                              uint32_t is_store) {
    osprey_on_mem_access(env, addr, (uint64_t)size, (uint64_t)pc, is_store);
}

void helper_osprey_mem_copy(CPUArchState *env, target_ulong src,
                            target_ulong dst, target_ulong size) {
    osprey_on_mem_copy(env, src, dst, size);
}

void helper_osprey_call(CPUArchState *env, target_ulong callee_pc,
                        target_ulong entry_sp) {
    osprey_on_call(env, callee_pc, entry_sp);
}

void helper_osprey_ret(CPUArchState *env, target_ulong pc,
                       target_ulong sp) {
    osprey_on_ret(env, pc, sp);
}

void helper_osprey_rsp_update(CPUArchState *env, target_ulong new_sp,
                               target_ulong pc) {
    osprey_on_rsp_update(env, new_sp, pc);
}

void helper_osprey_on_load(CPUArchState *env, uint32_t dst_reg,
                           target_ulong addr, target_ulong size) {
    /* Aligned native-width reload: restore the origin into dst_reg. */
    if (size == OSPREY_SHADOW_ALIGN && (addr & (OSPREY_SHADOW_ALIGN - 1)) == 0) {
        target_ulong value = 0;
        if (is_valid_address(addr, false)) {
            memcpy(&value, g2h(addr), sizeof(value));
        }
        osprey_on_mem_load_origin(env, dst_reg, addr, value);
    }
}

void helper_osprey_on_store(CPUArchState *env, uint32_t src_reg,
                            target_ulong addr, target_ulong size,
                            target_ulong src_val) {
    osprey_on_mem_store_origin(env, src_reg, addr, size, src_val);
}
