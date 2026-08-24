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
void helper_osprey_call(target_ulong call_pc, target_ulong ret_pc,
                        target_ulong callee_pc, target_ulong sp);
void helper_osprey_ret(target_ulong pc, target_ulong sp);

/* F04 points-to emission (defined below; called from the origin-shadow
 * spill/reload hooks). */
static void record_points_to(CPUArchState *env, target_ulong addr,
                             uint64_t size, target_ulong value);

#include "qemu/thread.h"
#include "snapshot.h"

#include <stdlib.h>
#include <string.h>

/* ------------------------------------------------------------------ */
/* Fact hashes and equality                                            */
/* ------------------------------------------------------------------ */

#define MIX64(h, v) do { \
    h ^= (uint64_t)(v) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2); \
} while (0)

static uint64_t hash_chunk(const OspreyChunk *c) {
    uint64_t h = osprey_chunk_key(c);
    MIX64(h, c->size);
    return h;
}

static uint64_t hash_addr(const OspreyAddress *a) {
    uint64_t h = osprey_region_key(&a->region);
    MIX64(h, a->offset);
    return h;
}

static bool eq_chunk(const OspreyChunk *a, const OspreyChunk *b) {
    return a->size == b->size && a->address.offset == b->address.offset &&
           osprey_region_key(&a->address.region) ==
               osprey_region_key(&b->address.region);
}

static bool eq_addr(const OspreyAddress *a, const OspreyAddress *b) {
    return a->offset == b->offset &&
           osprey_region_key(&a->region) == osprey_region_key(&b->region);
}

uint64_t osprey_access_hash(const OspreyAccessFact *f) {
    uint64_t h = f->pc;
    MIX64(h, f->is_store);
    MIX64(h, hash_chunk(&f->chunk));
    return h;
}
bool osprey_access_eq(const OspreyAccessFact *a, const OspreyAccessFact *b) {
    return a->pc == b->pc && a->is_store == b->is_store &&
           eq_chunk(&a->chunk, &b->chunk);
}

uint64_t osprey_base_hash(const OspreyBaseFact *f) {
    uint64_t h = f->pc;
    MIX64(h, hash_chunk(&f->chunk));
    MIX64(h, hash_addr(&f->base));
    return h;
}
bool osprey_base_eq(const OspreyBaseFact *a, const OspreyBaseFact *b) {
    return a->pc == b->pc && eq_chunk(&a->chunk, &b->chunk) &&
           eq_addr(&a->base, &b->base);
}

uint64_t osprey_copy_hash(const OspreyCopyFact *f) {
    uint64_t h = hash_chunk(&f->source);
    MIX64(h, hash_chunk(&f->destination));
    return h;
}
bool osprey_copy_eq(const OspreyCopyFact *a, const OspreyCopyFact *b) {
    return eq_chunk(&a->source, &b->source) &&
           eq_chunk(&a->destination, &b->destination);
}

uint64_t osprey_points_hash(const OspreyPointsToFact *f) {
    uint64_t h = hash_chunk(&f->pointer_chunk);
    MIX64(h, hash_addr(&f->target));
    return h;
}
bool osprey_points_eq(const OspreyPointsToFact *a, const OspreyPointsToFact *b) {
    return eq_chunk(&a->pointer_chunk, &b->pointer_chunk) &&
           eq_addr(&a->target, &b->target);
}

uint64_t osprey_alloc_hash(const OspreyMallocFact *f) {
    uint64_t h = f->site_pc;
    MIX64(h, f->requested_size);
    return h;
}
bool osprey_alloc_eq(const OspreyMallocFact *a, const OspreyMallocFact *b) {
    return a->site_pc == b->site_pc && a->requested_size == b->requested_size;
}

uint64_t osprey_region_instance_hash(const OspreyRegionInstance *f) {
    uint64_t h = osprey_region_key(&f->region);
    MIX64(h, f->raw_base);
    return h;
}
bool osprey_region_instance_eq(const OspreyRegionInstance *a,
                               const OspreyRegionInstance *b) {
    return a->raw_base == b->raw_base &&
           a->region.kind == b->region.kind &&
           a->region.code_image_id == b->region.code_image_id &&
           a->region.site_offset == b->region.site_offset;
}

uint64_t osprey_mayarray_hash(const OspreyMayArrayFact *f) {
    uint64_t h = hash_addr(&f->start);
    MIX64(h, f->element_count);
    MIX64(h, f->element_size);
    MIX64(h, f->evidence_kind);
    return h;
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
        run->first_dropped_key = hash(rec);
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
int osprey_table_insert_region(OspreySharedRun *run,
                               const OspreyRegionInstance *f) {
    return run_table_insert(run, OSPREY_TABLE_REGION, f,
                            (HashFn)osprey_region_instance_hash,
                            (VerifyFn)osprey_region_instance_eq, NULL);
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

typedef struct OspreyGlobalRegion {
    OspreyRegionId id;
    target_ulong base;
    uint64_t extent;
} OspreyGlobalRegion;

static OspreyGlobalRegion g_global;
static bool g_global_set = false;

typedef struct OspreyStackFrame {
    OspreyRegionId region;
    target_ulong entry_sp;
    target_ulong min_sp;
    bool precise;
} OspreyStackFrame;

static GArray *g_stack_frames = NULL; /* OspreyStackFrame */

typedef struct HeapInstance {
    OspreyRegionId region;   /* H_site */
    uint64_t instance_id;
    target_ulong base;
    uint64_t size;
    bool live;
} HeapInstance;

static GArray *g_heap_instances = NULL; /* HeapInstance */
static uint64_t g_next_heap_instance = 1;

/* Region-instance recorder (defined below with the allocation hooks;
 * used earlier by the image-global and stack-frame registration). */
static void record_region_instance(const OspreyRegionId *region,
                                   target_ulong raw_base,
                                   uint64_t extent);

void osprey_register_image_global(CPUArchState *env, target_ulong base,
                                  target_ulong size) {
    (void)env;
    g_global.id.kind = OSPREY_REGION_GLOBAL;
    g_global.id.code_image_id = 0;
    g_global.id.site_offset = 0;
    g_global.base = base;
    g_global.extent = size;
    g_global_set = true;
    record_region_instance(&g_global.id, base, (uint64_t)size);
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
            if (addr >= h->base && addr < h->base + h->size) {
                *region = h->region;
                *offset = (int64_t)(addr - h->base);
                return true;
            }
        }
    }
    /* 2. Main-image global data. */
    if (g_global_set && addr >= g_global.base &&
        addr < g_global.base + g_global.extent) {
        *region = g_global.id;
        *offset = (int64_t)(addr - g_global.base);
        return true;
    }
    /* 3. Stack frames: innermost live frame first.  Offsets are signed
     * relative to the entry SP (negative below it).  A frame grows to
     * cover accesses below its current min_sp, bounded by a window so an
     * unrelated deep address is not folded into a frame. */
    if (g_stack_frames != NULL) {
        for (guint i = g_stack_frames->len; i > 0; i--) {
            OspreyStackFrame *f = &g_array_index(g_stack_frames,
                                                 OspreyStackFrame, i - 1);
            if (addr >= f->entry_sp) {
                continue;
            }
            if (addr >= f->min_sp) {
                *region = f->region;
                *offset = (int64_t)addr - (int64_t)f->entry_sp;
                return true;
            }
            /* Access below min_sp: grow only within a bounded window. */
            if (addr >= f->entry_sp - 0x100000) {
                f->min_sp = addr;
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
    if (image_base == 0) {
        *out = (uint64_t)pc;
        return true;
    }
    if (pc < image_base || pc - image_base > 0x7ffffffffULL) {
        return false;
    }
    *out = (uint64_t)(pc - image_base);
    return true;
}

void osprey_on_call(target_ulong call_pc, target_ulong ret_pc,
                    target_ulong callee_pc, target_ulong sp) {
    (void)call_pc;
    (void)ret_pc;
    if (g_stack_frames == NULL) {
        g_stack_frames = g_array_new(FALSE, FALSE, sizeof(OspreyStackFrame));
    }
    OspreyStackFrame f;
    memset(&f, 0, sizeof(f));
    f.region.kind = OSPREY_REGION_STACK_FUNCTION;
    f.region.code_image_id = 0;
    f.precise = osprey_normalize_pc(callee_pc, &f.region.site_offset);
    f.entry_sp = sp;
    f.min_sp = sp >= sizeof(target_ulong) ? sp - sizeof(target_ulong) : 0;
    g_array_append_val(g_stack_frames, f);
    /* Stack instance extent is dynamic; record the entry SP as the raw
     * base with the observed span so the parent can map addresses. */
    record_region_instance(&f.region, sp, 0x100000);
}

void osprey_on_ret(target_ulong pc, target_ulong sp) {
    (void)pc;
    if (g_stack_frames == NULL || g_stack_frames->len == 0) {
        return;
    }
    OspreyStackFrame *top = &g_array_index(g_stack_frames, OspreyStackFrame,
                                           g_stack_frames->len - 1);
    if (sp < top->entry_sp) {
        /* Return below the frame entry: stack not unwound to entry; the
         * frame is imprecise but is still the current frame. */
        return;
    }
    g_array_set_size(g_stack_frames, g_stack_frames->len - 1);
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
            record_points_to(env, addr, size, src_val);
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
        record_points_to(env, addr, 8, value);
    }
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
            record_region_instance(&f->region, f->entry_sp, 0x100000);
        }
    }
    if (g_heap_instances != NULL) {
        for (guint i = 0; i < g_heap_instances->len; i++) {
            const HeapInstance *h = &g_array_index(
                g_heap_instances, HeapInstance, i);
            if (h->live) {
                record_region_instance(&h->region, h->base, h->size);
            }
        }
    }
    if (g_global_set) {
        record_region_instance(&g_global.id, g_global.base,
                               g_global.extent);
    }
}

void osprey_child_use_shared_run(OspreyContext *ctx, OspreySharedRun *run) {
    if (ctx == NULL || run == NULL) return;
    osprey_ensure_mutex();
    g_shared_run = run;
    osprey_backfill_instances();
}

/* Record one live canonical region instance into the shared run
 * (parent needs the raw base to map mutation addresses). */
static void record_region_instance(const OspreyRegionId *region,
                                   target_ulong raw_base,
                                   uint64_t extent) {
    OspreySharedRun *run = g_shared_run;
    if (run == NULL) return;
    OspreyRegionInstance f;
    memset(&f, 0, sizeof(f));
    f.region = *region;
    f.raw_base = (uint64_t)raw_base;
    f.extent = extent;
    f.sample_support = 1;
    qemu_mutex_lock(&g_shared_mutex);
    osprey_table_insert_region(run, &f);
    qemu_mutex_unlock(&g_shared_mutex);
}

void osprey_on_alloc_success(CPUArchState *env, target_ulong base,
                             target_ulong size, target_ulong site_pc) {
    if (base == 0 && size != 0) return; /* failure: no object */
    if (g_heap_instances == NULL) {
        g_heap_instances = g_array_new(FALSE, FALSE, sizeof(HeapInstance));
    }
    /* A new instance even when the numeric base was reused. */
    HeapInstance h;
    memset(&h, 0, sizeof(h));
    h.region.kind = OSPREY_REGION_HEAP_SITE;
    h.region.code_image_id = 0;
    h.region.site_offset = (uint64_t)site_pc;
    h.instance_id = g_next_heap_instance++;
    h.base = base;
    h.size = size;
    h.live = true;
    g_array_append_val(g_heap_instances, h);

    record_region_instance(&h.region, base, (uint64_t)size);

    /* F05: successful-return requested size. */
    OspreySharedRun *run = g_shared_run;
    if (run != NULL) {
        OspreyMallocFact fact;
        memset(&fact, 0, sizeof(fact));
        fact.site_pc = (uint64_t)site_pc;
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
        o->producer_pc = (uint64_t)site_pc;
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
    OspreySharedRun *run = g_shared_run;
    if (run != NULL) {
        OspreyMallocFact fact;
        memset(&fact, 0, sizeof(fact));
        fact.site_pc = (uint64_t)site_pc;
        fact.requested_size = -1; /* explicit failure state */
        fact.sample_support = 1;
        qemu_mutex_lock(&g_shared_mutex);
        osprey_table_insert_alloc(run, &fact);
        qemu_mutex_unlock(&g_shared_mutex);
    }
}

void osprey_on_free(CPUArchState *env, target_ulong base,
                    target_ulong site_pc) {
    (void)env;
    (void)site_pc;
    if (base == 0 || g_heap_instances == NULL) return;
    for (guint i = 0; i < g_heap_instances->len; i++) {
        HeapInstance *h = &g_array_index(g_heap_instances, HeapInstance, i);
        if (h->live && h->base == base) {
            h->live = false;
            return;
        }
    }
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
                             uint64_t size, target_ulong value) {
    OspreySharedRun *run = g_shared_run;
    if (run == NULL) return;
    OspreyRegionId preg, treg;
    int64_t poff, toff;
    if (!osprey_region_of_addr(env, addr, &preg, &poff, false)) {
        run->bad_region = 1;
        return;
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
                OspreyBaseFact bf;
                memset(&bf, 0, sizeof(bf));
                bf.pc = pc;
                bf.chunk = chunk;
                bf.base = b->address;
                bf.sample_support = 1;
                qemu_mutex_lock(&g_shared_mutex);
                osprey_table_insert_base(run, &bf);
                qemu_mutex_unlock(&g_shared_mutex);
            }
        } else if (have_ea && index_reg >= 0 && index_reg < CPU_NB_REGS &&
                   scale == 1) {
            OspreyRegOrigin *ix = &st->ea_index_origin;
            if (ix->valid && ix->kind == OSPREY_ORIGIN_ADDRESS &&
                ix->concrete_value == index_val) {
                OspreyBaseFact bf;
                memset(&bf, 0, sizeof(bf));
                bf.pc = pc;
                bf.chunk = chunk;
                bf.base = ix->address;
                bf.sample_support = 1;
                qemu_mutex_lock(&g_shared_mutex);
                osprey_table_insert_base(run, &bf);
                qemu_mutex_unlock(&g_shared_mutex);
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
            "[bad-region %u] [bad-arith %u] [first-kind %u] [first-key %lx]\n",
            tag, run->sample_id, run->overflow, run->bad_region,
            run->bad_arithmetic, run->first_dropped_kind,
            (unsigned long)run->first_dropped_key);
}

/* ------------------------------------------------------------------ */
/* Parent-side merge + analysis entry                                  */
/* ------------------------------------------------------------------ */

/* ------------------------------------------------------------------ */
/* Parent-side merge + analysis entry                                  */
/* ------------------------------------------------------------------ */

/* Merge one completed sample (patch-0/iter-1 child run) into the
 * committed parent tables.  Duplicates merge support in place; the
 * merged record keeps the union of sample support.  Returns
 * OSPREY_INCOMPLETE_FACTS when the sample overflowed (the model must
 * not be installed from incomplete facts). */
OspreyStatus osprey_parent_merge_sample(OspreyContext *ctx,
                                         const OspreySharedRun *run) {
    if (ctx == NULL || run == NULL) return OSPREY_DISABLED;
    if (run->overflow) {
        osprey_log_sticky(run, "incomplete");
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
                if (f->extent > d->extent) d->extent = f->extent;
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
    return OSPREY_OK;
}

/* Analyze entry: Stage 2 deterministic closure, then (later stages)
 * inference and decoding. */
OspreyStatus osprey_analyze(OspreyContext *ctx) {
    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    OspreyStatus st = osprey_stage2_closure(ctx);
    if (st != OSPREY_OK && st != OSPREY_DISABLED) {
        log_msg("[osprey] [done] [status %d] [stages closure]\n", st);
        ctx->last_status = st;
        return st;
    }
    /* Stage 3a: secondary deterministic rules (CB02-CB09, CC04/CC05,
     * CD07/CD08); CC07 folding happens after the first BP pass. */
    st = osprey_stage2_secondary(ctx);
    if (st != OSPREY_OK && st != OSPREY_DISABLED) {
        log_msg("[osprey] [done] [status %d] [stages secondary]\n", st);
        ctx->last_status = st;
        return st;
    }
    /* Stage 3b: exact component solving + loopy BP + CC07 folding. */
    st = osprey_infer(ctx);
    if (st != OSPREY_OK && st != OSPREY_DISABLED &&
        st != OSPREY_NON_CONVERGED) {
        log_msg("[osprey] [done] [status %d] [stages inference]\n", st);
        ctx->last_status = st;
        return st;
    }
    /* Stage 4: consistent decoding into the OspreyModel (also on
     * non-convergence: retain the best damped iterate). */
    OspreyStatus d = osprey_decode(ctx);
    if (d != OSPREY_OK && d != OSPREY_DISABLED) {
        log_msg("[osprey] [done] [status %d] [stages decode]\n", d);
        ctx->last_status = d;
        return d;
    }
    log_msg("[osprey] [done] [status %d] [stages closure+secondary+infer+decode]\n",
            (int)st);
    ctx->last_status = st;
    return st;
}

const OspreyModel *osprey_model(const OspreyContext *ctx) {
    return ctx ? ctx->model : NULL;
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

void helper_osprey_call(target_ulong call_pc, target_ulong ret_pc,
                        target_ulong callee_pc, target_ulong sp) {
    osprey_on_call(call_pc, ret_pc, callee_pc, sp);
}

void helper_osprey_ret(target_ulong pc, target_ulong sp) {
    osprey_on_ret(pc, sp);
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
