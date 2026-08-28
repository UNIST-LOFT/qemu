/*
 * Intentionally slow Stage 3.1 oracle.  This file uses direct nested
 * loops and private comparators; it does not call the production relation
 * builder, indexes, or comparators.
 */

#include "osprey.h"
#include "osprey-internal.h"

#include <inttypes.h>
#include <limits.h>
#include <string.h>

bool stage3_reference_build(const OspreyContext *ctx, OspreyRelations **out);

static int ref_u64(uint64_t a, uint64_t b)
{
    return a < b ? -1 : a != b;
}

static int ref_i64(int64_t a, int64_t b)
{
    return a < b ? -1 : a != b;
}

static bool ref_same_region(const OspreyRegionId *a,
                            const OspreyRegionId *b)
{
    return a->kind == b->kind && a->code_image_id == b->code_image_id &&
           a->site_offset == b->site_offset;
}

static int ref_region_cmp(const OspreyRegionId *a, const OspreyRegionId *b)
{
    int c = ref_u64(a->kind, b->kind);
    if (c != 0) return c;
    c = ref_u64(a->code_image_id, b->code_image_id);
    if (c != 0) return c;
    return ref_u64(a->site_offset, b->site_offset);
}

static int ref_address_cmp(const OspreyAddress *a, const OspreyAddress *b)
{
    int c = ref_region_cmp(&a->region, &b->region);
    if (c != 0) return c;
    return ref_i64(a->offset, b->offset);
}

static int ref_chunk_cmp(const OspreyChunk *a, const OspreyChunk *b)
{
    int c = ref_address_cmp(&a->address, &b->address);
    if (c != 0) return c;
    return ref_u64(a->size, b->size);
}

static bool ref_logical_equal(const OspreyLogicalAccess *a,
                              const OspreyLogicalAccess *b)
{
    return a->pc == b->pc && ref_chunk_cmp(&a->chunk, &b->chunk) == 0;
}

static int ref_logical_cmp(gconstpointer ap, gconstpointer bp)
{
    const OspreyLogicalAccess *a = ap;
    const OspreyLogicalAccess *b = bp;
    int c = ref_u64(a->pc, b->pc);
    if (c != 0) return c;
    return ref_chunk_cmp(&a->chunk, &b->chunk);
}

static uint32_t ref_sat32(uint32_t a, uint32_t b)
{
    return UINT32_MAX - a < b ? UINT32_MAX : a + b;
}

static uint64_t ref_sat64(uint64_t a, uint64_t b)
{
    return UINT64_MAX - a < b ? UINT64_MAX : a + b;
}

static uint64_t ref_gcd64(uint64_t a, uint64_t b)
{
    while (b != 0) {
        uint64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int ref_insn_chunk_cmp(gconstpointer ap, gconstpointer bp)
{
    const OspreyInsnChunkRelation *a = ap;
    const OspreyInsnChunkRelation *b = bp;
    int c = ref_u64(a->pc, b->pc);
    return c != 0 ? c : ref_chunk_cmp(&a->chunk, &b->chunk);
}

static int ref_chunk_relation_cmp(gconstpointer ap, gconstpointer bp)
{
    return ref_chunk_cmp(&((const OspreyChunkRelation *)ap)->chunk,
                         &((const OspreyChunkRelation *)bp)->chunk);
}

static int ref_insn_region_cmp(gconstpointer ap, gconstpointer bp)
{
    const OspreyInsnRegionRelation *a = ap;
    const OspreyInsnRegionRelation *b = bp;
    int c = ref_u64(a->pc, b->pc);
    return c != 0 ? c : ref_region_cmp(&a->region, &b->region);
}

static int ref_insn_region_address_cmp(gconstpointer ap, gconstpointer bp)
{
    const OspreyInsnRegionAddressRelation *a = ap;
    const OspreyInsnRegionAddressRelation *b = bp;
    int c = ref_u64(a->pc, b->pc);
    if (c != 0) return c;
    c = ref_region_cmp(&a->region, &b->region);
    if (c != 0) return c;
    c = ref_address_cmp(&a->address, &b->address);
    return c != 0 ? c : ref_u64(a->count, b->count);
}

static int ref_alloc_cmp(gconstpointer ap, gconstpointer bp)
{
    const OspreyAllocRelation *a = ap;
    const OspreyAllocRelation *b = bp;
    int c = ref_u64(a->site_pc, b->site_pc);
    return c != 0 ? c : ref_u64(a->size, b->size);
}

static int ref_hint_cmp(gconstpointer ap, gconstpointer bp)
{
    const OspreyHintRelation *a = ap;
    const OspreyHintRelation *b = bp;
    int c = ref_address_cmp(&a->a1, &b->a1);
    if (c != 0) return c;
    c = ref_address_cmp(&a->a2, &b->a2);
    return c != 0 ? c : ref_i64(a->size, b->size);
}

static OspreyRelations *ref_relations_new(void)
{
    OspreyRelations *r = g_new0(OspreyRelations, 1);
#define NEW(_field, _type) r->_field = g_array_new(FALSE, FALSE, sizeof(_type))
    NEW(logical_accesses, OspreyLogicalAccess);
    NEW(r01_accessed, OspreyInsnChunkRelation);
    NEW(r02_accessed, OspreyChunkRelation);
    NEW(r03_single_chunk, OspreyInsnRegionRelation);
    NEW(r04_multi_chunk, OspreyInsnRegionRelation);
    NEW(r05_high_address, OspreyInsnRegionAddressRelation);
    NEW(r06_low_address, OspreyInsnRegionAddressRelation);
    NEW(r07_most_frequent, OspreyInsnRegionAddressRelation);
    NEW(r08_constant_alloc, OspreyAllocRelation);
    NEW(r09_alloc_unit, OspreyAllocRelation);
    NEW(r10_data_flow, OspreyHintRelation);
    NEW(r11_unified_access, OspreyHintRelation);
    NEW(r12_points_to, OspreyHintRelation);
#undef NEW
    return r;
}

static void ref_copy_logical(const OspreyContext *ctx, OspreyRelations *r)
{
    GArray *tmp = g_array_new(FALSE, FALSE, sizeof(OspreyLogicalAccess));
    for (guint i = 0; ctx->logical_access_facts != NULL &&
                       i < ctx->logical_access_facts->len; i++) {
        OspreyLogicalAccess row = g_array_index(
            ctx->logical_access_facts, OspreyLogicalAccess, i);
        g_array_append_val(tmp, row);
    }
    g_array_sort(tmp, ref_logical_cmp);
    for (guint i = 0; i < tmp->len; i++) {
        OspreyLogicalAccess row = g_array_index(tmp, OspreyLogicalAccess, i);
        if (r->logical_accesses->len != 0) {
            OspreyLogicalAccess *last = &g_array_index(
                r->logical_accesses, OspreyLogicalAccess,
                r->logical_accesses->len - 1);
            if (ref_logical_equal(last, &row)) {
                last->dynamic_count = ref_sat32(last->dynamic_count,
                                                row.dynamic_count);
                last->sample_support = ref_sat32(last->sample_support,
                                                 row.sample_support);
                continue;
            }
        }
        g_array_append_val(r->logical_accesses, row);
    }
    g_array_free(tmp, TRUE);
}

static void ref_build_r01_r02(OspreyRelations *r)
{
    for (guint i = 0; i < r->logical_accesses->len; i++) {
        const OspreyLogicalAccess *a = &g_array_index(
            r->logical_accesses, OspreyLogicalAccess, i);
        OspreyInsnChunkRelation r01;
        memset(&r01, 0, sizeof(r01));
        r01.pc = a->pc;
        r01.chunk = a->chunk;
        g_array_append_val(r->r01_accessed, r01);
        bool found = false;
        for (guint j = 0; j < r->r02_accessed->len; j++) {
            if (ref_chunk_cmp(&a->chunk,
                              &g_array_index(r->r02_accessed,
                                             OspreyChunkRelation, j).chunk) == 0) {
                found = true;
                break;
            }
        }
        if (!found) {
            OspreyChunkRelation row;
            memset(&row, 0, sizeof(row));
            row.chunk = a->chunk;
            g_array_append_val(r->r02_accessed, row);
        }
    }
    g_array_sort(r->r01_accessed, ref_insn_chunk_cmp);
    g_array_sort(r->r02_accessed, ref_chunk_relation_cmp);
}

static bool ref_same_group(const OspreyLogicalAccess *a,
                           const OspreyLogicalAccess *b)
{
    return a->pc == b->pc && ref_same_region(&a->chunk.address.region,
                                             &b->chunk.address.region);
}

static void ref_build_r03_r07(OspreyRelations *r)
{
    guint begin = 0;
    while (begin < r->logical_accesses->len) {
        const OspreyLogicalAccess *first = &g_array_index(
            r->logical_accesses, OspreyLogicalAccess, begin);
        guint end = begin + 1;
        while (end < r->logical_accesses->len && ref_same_group(
                   first, &g_array_index(r->logical_accesses,
                                         OspreyLogicalAccess, end))) {
            end++;
        }
        OspreyInsnRegionRelation rr;
        memset(&rr, 0, sizeof(rr));
        rr.pc = first->pc;
        rr.region = first->chunk.address.region;
        if (end - begin == 1) g_array_append_val(r->r03_single_chunk, rr);
        else g_array_append_val(r->r04_multi_chunk, rr);

        const OspreyLogicalAccess *low = first;
        const OspreyLogicalAccess *high = first;
        uint32_t maximum = first->dynamic_count;
        for (guint i = begin + 1; i < end; i++) {
            const OspreyLogicalAccess *row = &g_array_index(
                r->logical_accesses, OspreyLogicalAccess, i);
            if (row->chunk.address.offset < low->chunk.address.offset) low = row;
            if (row->chunk.address.offset > high->chunk.address.offset) high = row;
            if (row->dynamic_count > maximum) maximum = row->dynamic_count;
        }
        OspreyInsnRegionAddressRelation ext;
        memset(&ext, 0, sizeof(ext));
        ext.pc = first->pc;
        ext.region = first->chunk.address.region;
        ext.address = high->chunk.address;
        g_array_append_val(r->r05_high_address, ext);
        ext.address = low->chunk.address;
        g_array_append_val(r->r06_low_address, ext);

        for (guint i = begin; i < end; ) {
            const OspreyLogicalAccess *row = &g_array_index(
                r->logical_accesses, OspreyLogicalAccess, i);
            int64_t offset = row->chunk.address.offset;
            uint32_t address_max = row->dynamic_count;
            guint next = i + 1;
            while (next < end &&
                   g_array_index(r->logical_accesses, OspreyLogicalAccess,
                                 next).chunk.address.offset == offset) {
                const OspreyLogicalAccess *same = &g_array_index(
                    r->logical_accesses, OspreyLogicalAccess, next);
                if (same->dynamic_count > address_max) {
                    address_max = same->dynamic_count;
                }
                next++;
            }
            if (address_max == maximum) {
                OspreyInsnRegionAddressRelation most;
                memset(&most, 0, sizeof(most));
                most.pc = first->pc;
                most.region = first->chunk.address.region;
                most.address = row->chunk.address;
                most.count = address_max;
                g_array_append_val(r->r07_most_frequent, most);
            }
            i = next;
        }
        begin = end;
    }
    g_array_sort(r->r03_single_chunk, ref_insn_region_cmp);
    g_array_sort(r->r04_multi_chunk, ref_insn_region_cmp);
    g_array_sort(r->r05_high_address, ref_insn_region_address_cmp);
    g_array_sort(r->r06_low_address, ref_insn_region_address_cmp);
    g_array_sort(r->r07_most_frequent, ref_insn_region_address_cmp);
}

static bool ref_build_r08_r09(const OspreyContext *ctx, OspreyRelations *r)
{
    GArray *rows = g_array_new(FALSE, FALSE, sizeof(OspreyAllocRelation));
    for (guint i = 0; i < ctx->alloc_facts->len; i++) {
        const OspreyMallocFact *fact = &g_array_index(
            ctx->alloc_facts, OspreyMallocFact, i);
        if (fact->requested_size > (uint64_t)INT64_MAX) {
            g_array_free(rows, TRUE);
            return false;
        }
        OspreyAllocRelation row = { fact->site_pc, fact->requested_size };
        g_array_append_val(rows, row);
    }
    g_array_sort(rows, ref_alloc_cmp);
    guint begin = 0;
    while (begin < rows->len) {
        guint end = begin + 1;
        uint64_t site = g_array_index(rows, OspreyAllocRelation, begin).site_pc;
        while (end < rows->len &&
               g_array_index(rows, OspreyAllocRelation, end).site_pc == site) {
            end++;
        }
        GArray *sizes = g_array_new(FALSE, FALSE, sizeof(uint64_t));
        for (guint i = begin; i < end; i++) {
            uint64_t size = g_array_index(rows, OspreyAllocRelation, i).size;
            if (sizes->len == 0 ||
                g_array_index(sizes, uint64_t, sizes->len - 1) != size) {
                g_array_append_val(sizes, size);
            }
        }
        if (sizes->len == 1) {
            OspreyAllocRelation row = { site,
                g_array_index(sizes, uint64_t, 0) };
            g_array_append_val(r->r08_constant_alloc, row);
        } else if (sizes->len >= 2) {
            uint64_t gcd = 0;
            for (guint i = 1; i < sizes->len; i++) {
                uint64_t previous = g_array_index(sizes, uint64_t, i - 1);
                uint64_t current = g_array_index(sizes, uint64_t, i);
                uint64_t difference = current - previous;
                gcd = gcd == 0 ? difference : ref_gcd64(gcd, difference);
            }
            if (gcd == 0) {
                g_array_free(sizes, TRUE);
                g_array_free(rows, TRUE);
                return false;
            }
            OspreyAllocRelation row = { site, gcd };
            g_array_append_val(r->r09_alloc_unit, row);
        }
        g_array_free(sizes, TRUE);
        begin = end;
    }
    g_array_sort(r->r08_constant_alloc, ref_alloc_cmp);
    g_array_sort(r->r09_alloc_unit, ref_alloc_cmp);
    g_array_free(rows, TRUE);
    return true;
}

static bool ref_sub(const OspreyAddress *a, const OspreyAddress *b,
                    int64_t *out)
{
    if (!ref_same_region(&a->region, &b->region)) return false;
    return !__builtin_sub_overflow(a->offset, b->offset, out);
}

static void ref_hint_add(GArray *hints, const OspreyAddress *a1,
                         const OspreyAddress *a2, int64_t size,
                         uint8_t kind)
{
    for (guint i = 0; i < hints->len; i++) {
        OspreyHintRelation *row = &g_array_index(hints, OspreyHintRelation, i);
        if (row->kind == kind && row->size == size &&
            ref_address_cmp(&row->a1, a1) == 0 &&
            ref_address_cmp(&row->a2, a2) == 0) {
            row->witness_count = ref_sat64(row->witness_count, 1);
            return;
        }
    }
    OspreyHintRelation row;
    memset(&row, 0, sizeof(row));
    row.a1 = *a1;
    row.a2 = *a2;
    row.size = size;
    row.kind = kind;
    row.witness_count = 1;
    g_array_append_val(hints, row);
}

static bool ref_copy_equal(const OspreyCopyFact *a,
                           const OspreyCopyFact *b)
{
    return ref_chunk_cmp(&a->source, &b->source) == 0 &&
           ref_chunk_cmp(&a->destination, &b->destination) == 0;
}

static bool ref_build_r10(const OspreyContext *ctx, OspreyRelations *r)
{
    GArray *facts = g_array_new(FALSE, FALSE, sizeof(OspreyCopyFact));
    for (guint i = 0; i < ctx->copy_facts->len; i++) {
        const OspreyCopyFact *candidate = &g_array_index(
            ctx->copy_facts, OspreyCopyFact, i);
        bool duplicate = false;
        for (guint j = 0; j < facts->len; j++) {
            if (ref_copy_equal(candidate, &g_array_index(
                    facts, OspreyCopyFact, j))) {
                duplicate = true;
                break;
            }
        }
        if (!duplicate) g_array_append_val(facts, *candidate);
    }

    for (guint i = 0; i < facts->len; i++) {
        const OspreyCopyFact *a = &g_array_index(facts, OspreyCopyFact, i);
        for (guint j = i + 1; j < facts->len; j++) {
            const OspreyCopyFact *b = &g_array_index(facts,
                                                      OspreyCopyFact, j);
            int64_t ds, dd;
            if (ref_same_region(&a->source.address.region,
                                &b->source.address.region)) {
                if (!ref_sub(&b->source.address, &a->source.address, &ds)) {
                    goto fail;
                }
            } else {
                continue;
            }
            if (!ref_same_region(&a->destination.address.region,
                                 &b->destination.address.region)) continue;
            if (!ref_sub(&b->destination.address, &a->destination.address,
                         &dd)) goto fail;
            if (ds == 0 || ds != dd) continue;
            if (ds > 0) {
                ref_hint_add(r->r10_data_flow, &a->source.address,
                             &a->destination.address, ds,
                             OSPREY_RELATION_DATA_FLOW);
            } else {
                int64_t rs, rd;
                if (!ref_sub(&a->source.address, &b->source.address, &rs) ||
                    !ref_sub(&a->destination.address, &b->destination.address,
                             &rd) || rs != rd || rs <= 0) {
                    goto fail;
                }
                ref_hint_add(r->r10_data_flow, &b->source.address,
                             &b->destination.address, rs,
                             OSPREY_RELATION_DATA_FLOW);
            }
        }
    }
    g_array_sort(r->r10_data_flow, ref_hint_cmp);
    g_array_free(facts, TRUE);
    return true;

fail:
    g_array_free(facts, TRUE);
    return false;
}

typedef struct RefPair {
    uint64_t pc;
    OspreyChunk first;
    OspreyChunk second;
} RefPair;

static int ref_pair_cmp(gconstpointer ap, gconstpointer bp)
{
    const RefPair *a = ap;
    const RefPair *b = bp;
    int c = ref_u64(a->pc, b->pc);
    if (c != 0) return c;
    c = ref_chunk_cmp(&a->first, &b->first);
    return c != 0 ? c : ref_chunk_cmp(&a->second, &b->second);
}

static bool ref_build_r11(const OspreyRelations *r, OspreyRelations *out)
{
    GArray *pairs = g_array_new(FALSE, FALSE, sizeof(RefPair));
    for (guint i = 0; i < r->r01_accessed->len; i++) {
        const OspreyInsnChunkRelation *a = &g_array_index(
            r->r01_accessed, OspreyInsnChunkRelation, i);
        for (guint j = i + 1; j < r->r01_accessed->len; j++) {
            const OspreyInsnChunkRelation *b = &g_array_index(
                r->r01_accessed, OspreyInsnChunkRelation, j);
            if (a->pc != b->pc) break;
            RefPair pair;
            memset(&pair, 0, sizeof(pair));
            pair.pc = a->pc;
            if (ref_chunk_cmp(&a->chunk, &b->chunk) < 0) {
                pair.first = a->chunk;
                pair.second = b->chunk;
            } else {
                pair.first = b->chunk;
                pair.second = a->chunk;
            }
            g_array_append_val(pairs, pair);
        }
    }
    g_array_sort(pairs, ref_pair_cmp);
    for (guint i = 0; i < pairs->len; i++) {
        const RefPair *a = &g_array_index(pairs, RefPair, i);
        for (guint j = i + 1; j < pairs->len; j++) {
            const RefPair *b = &g_array_index(pairs, RefPair, j);
            if (a->pc == b->pc) continue;
            if (!ref_same_region(&a->first.address.region,
                                 &b->first.address.region) ||
                !ref_same_region(&a->second.address.region,
                                 &b->second.address.region)) continue;
            int64_t d1, d2;
            if (!ref_sub(&b->first.address, &a->first.address, &d1) ||
                !ref_sub(&b->second.address, &a->second.address, &d2)) {
                g_array_free(pairs, TRUE);
                return false;
            }
            if (d1 == 0 || d1 != d2) continue;
            if (d1 > 0) {
                ref_hint_add(out->r11_unified_access, &a->first.address,
                             &a->second.address, d1,
                             OSPREY_RELATION_UNIFIED_ACCESS);
            } else {
                int64_t rd1, rd2;
                if (!ref_sub(&a->first.address, &b->first.address, &rd1) ||
                    !ref_sub(&a->second.address, &b->second.address, &rd2) ||
                    rd1 != rd2 || rd1 <= 0) {
                    g_array_free(pairs, TRUE);
                    return false;
                }
                ref_hint_add(out->r11_unified_access, &b->first.address,
                             &b->second.address, rd1,
                             OSPREY_RELATION_UNIFIED_ACCESS);
            }
        }
    }
    g_array_sort(out->r11_unified_access, ref_hint_cmp);
    g_array_free(pairs, TRUE);
    return true;
}

typedef struct RefBase {
    OspreyAddress base;
    OspreyChunk chunk;
} RefBase;

typedef struct RefPoint {
    OspreyChunk pointer_chunk;
    OspreyAddress target;
} RefPoint;

static int ref_base_cmp(gconstpointer ap, gconstpointer bp)
{
    const RefBase *a = ap;
    const RefBase *b = bp;
    int c = ref_address_cmp(&a->base, &b->base);
    return c != 0 ? c : ref_chunk_cmp(&a->chunk, &b->chunk);
}

static int ref_point_cmp(gconstpointer ap, gconstpointer bp)
{
    const RefPoint *a = ap;
    const RefPoint *b = bp;
    int c = ref_chunk_cmp(&a->pointer_chunk, &b->pointer_chunk);
    return c != 0 ? c : ref_address_cmp(&a->target, &b->target);
}

static bool ref_chunk_is_accessed(const OspreyRelations *r,
                                  const OspreyChunk *chunk)
{
    for (guint i = 0; i < r->r02_accessed->len; i++) {
        if (ref_chunk_cmp(chunk, &g_array_index(r->r02_accessed,
                                                OspreyChunkRelation, i).chunk) ==
            0) return true;
    }
    return false;
}

static bool ref_build_r12(const OspreyContext *ctx, const OspreyRelations *r,
                          OspreyRelations *out)
{
    GArray *bases = g_array_new(FALSE, FALSE, sizeof(RefBase));
    GArray *points = g_array_new(FALSE, FALSE, sizeof(RefPoint));
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        const OspreyBaseFact *fact = &g_array_index(ctx->base_facts,
                                                    OspreyBaseFact, i);
        if (!ref_chunk_is_accessed(r, &fact->chunk)) continue;
        RefBase row = { fact->base, fact->chunk };
        g_array_append_val(bases, row);
    }
    g_array_sort(bases, ref_base_cmp);
    guint ub = 0;
    for (guint i = 0; i < bases->len; i++) {
        RefBase row = g_array_index(bases, RefBase, i);
        if (ub != 0 && ref_base_cmp(&row, &g_array_index(
                bases, RefBase, ub - 1)) == 0) continue;
        g_array_index(bases, RefBase, ub++) = row;
    }
    g_array_set_size(bases, ub);
    for (guint i = 0; i < ctx->points_facts->len; i++) {
        const OspreyPointsToFact *fact = &g_array_index(
            ctx->points_facts, OspreyPointsToFact, i);
        RefPoint row = { fact->pointer_chunk, fact->target };
        g_array_append_val(points, row);
    }
    g_array_sort(points, ref_point_cmp);
    guint up = 0;
    for (guint i = 0; i < points->len; i++) {
        RefPoint row = g_array_index(points, RefPoint, i);
        if (up != 0 && ref_point_cmp(&row, &g_array_index(
                points, RefPoint, up - 1)) == 0) continue;
        g_array_index(points, RefPoint, up++) = row;
    }
    g_array_set_size(points, up);

    guint begin = 0;
    while (begin < points->len) {
        const RefPoint *first = &g_array_index(points, RefPoint, begin);
        guint end = begin + 1;
        while (end < points->len &&
               ref_chunk_cmp(&first->pointer_chunk,
                             &g_array_index(points, RefPoint, end)
                                  .pointer_chunk) == 0) end++;
        for (guint x = begin; x < end; x++) {
            for (guint y = x + 1; y < end; y++) {
                OspreyAddress a1 = g_array_index(points, RefPoint, x).target;
                OspreyAddress a2 = g_array_index(points, RefPoint, y).target;
                if (ref_address_cmp(&a1, &a2) > 0) {
                    OspreyAddress swap = a1;
                    a1 = a2;
                    a2 = swap;
                }
                for (guint i = 0; i < bases->len; i++) {
                    const RefBase *bs = &g_array_index(bases, RefBase, i);
                    if (ref_address_cmp(&bs->base, &a1) != 0 ||
                        !ref_same_region(&bs->chunk.address.region,
                                         &a1.region)) continue;
                    int64_t ds;
                    if (!ref_sub(&bs->chunk.address, &a1, &ds)) {
                        g_array_free(bases, TRUE);
                        g_array_free(points, TRUE);
                        return false;
                    }
                    if (ds <= 0) continue;
                    for (guint j = 0; j < bases->len; j++) {
                        const RefBase *bd = &g_array_index(bases, RefBase, j);
                        if (ref_address_cmp(&bd->base, &a2) != 0 ||
                            !ref_same_region(&bd->chunk.address.region,
                                             &a2.region)) continue;
                        int64_t dd;
                        if (!ref_sub(&bd->chunk.address, &a2, &dd)) {
                            g_array_free(bases, TRUE);
                            g_array_free(points, TRUE);
                            return false;
                        }
                        if (ds == dd) {
                            ref_hint_add(out->r12_points_to, &a1, &a2, ds,
                                         OSPREY_RELATION_POINTS_TO);
                        }
                    }
                }
            }
        }
        begin = end;
    }
    g_array_sort(out->r12_points_to, ref_hint_cmp);
    g_array_free(bases, TRUE);
    g_array_free(points, TRUE);
    return true;
}

bool stage3_reference_build(const OspreyContext *ctx, OspreyRelations **out)
{
    OspreyRelations *r;
    if (ctx == NULL || out == NULL) return false;
    r = ref_relations_new();
    ref_copy_logical(ctx, r);
    ref_build_r01_r02(r);
    ref_build_r03_r07(r);
    if (!ref_build_r08_r09(ctx, r) || !ref_build_r10(ctx, r) ||
        !ref_build_r11(r, r) || !ref_build_r12(ctx, r, r)) {
        osprey_relations_free(r);
        return false;
    }
    *out = r;
    return true;
}
