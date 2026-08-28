/*
 * OSPREY Stage 3.1: deterministic relations H01-H07 and R01-R12.
 *
 * This translation unit deliberately stops before predicate interning and
 * factor construction.  It consumes only the parent-local logical access
 * projection and the already validated Stage 2 fact arrays.  All emitted
 * relations are sorted by explicit semantic comparators; hash tables below
 * are lookup accelerators, never sources of output order.
 */

#include "osprey.h"
#include "osprey-internal.h"

#include <inttypes.h>
#include <limits.h>
#include <string.h>

/* ------------------------------------------------------------------ */
/* Canonical scalar helpers                                            */
/* ------------------------------------------------------------------ */

typedef enum RelationSubResult {
    RELATION_SUB_DIFFERENT_REGION = 0,
    RELATION_SUB_OK = 1,
    RELATION_SUB_OVERFLOW = -1,
} RelationSubResult;

static int cmp_u64(uint64_t a, uint64_t b)
{
    return a < b ? -1 : a != b;
}

static int cmp_i64(int64_t a, int64_t b)
{
    return a < b ? -1 : a != b;
}

bool osprey_relation_same_region(const OspreyRegionId *a,
                                 const OspreyRegionId *b)
{
    return a != NULL && b != NULL && a->kind == b->kind &&
           a->code_image_id == b->code_image_id &&
           a->site_offset == b->site_offset;
}

static int relation_region_compare(const OspreyRegionId *a,
                                   const OspreyRegionId *b)
{
    int c = cmp_u64((uint64_t)a->kind, (uint64_t)b->kind);
    if (c != 0) return c;
    c = cmp_u64(a->code_image_id, b->code_image_id);
    if (c != 0) return c;
    return cmp_u64(a->site_offset, b->site_offset);
}

static int relation_address_compare(const OspreyAddress *a,
                                    const OspreyAddress *b)
{
    int c = relation_region_compare(&a->region, &b->region);
    if (c != 0) return c;
    return cmp_i64(a->offset, b->offset);
}

static int relation_chunk_compare(const OspreyChunk *a,
                                  const OspreyChunk *b)
{
    int c = relation_address_compare(&a->address, &b->address);
    if (c != 0) return c;
    return cmp_u64(a->size, b->size);
}

static RelationSubResult relation_sub_checked(const OspreyAddress *a,
                                              const OspreyAddress *b,
                                              int64_t *out)
{
    if (!osprey_relation_same_region(&a->region, &b->region)) {
        return RELATION_SUB_DIFFERENT_REGION;
    }
    if (!osprey_check_sub(a->offset, b->offset, out)) {
        return RELATION_SUB_OVERFLOW;
    }
    return RELATION_SUB_OK;
}

bool osprey_relation_offset(const OspreyAddress *a,
                            const OspreyAddress *b, int64_t *out)
{
    return a != NULL && b != NULL &&
           relation_sub_checked(a, b, out) == RELATION_SUB_OK;
}

bool osprey_relation_adjacent_chunk(const OspreyChunk *a,
                                    const OspreyChunk *b)
{
    int64_t end;
    if (a == NULL || b == NULL ||
        !osprey_relation_same_region(&a->address.region,
                                     &b->address.region) ||
        a->size > (uint64_t)INT64_MAX) {
        return false;
    }
    if (!osprey_check_add(a->address.offset, (int64_t)a->size, &end)) {
        return false;
    }
    return end == b->address.offset;
}

bool osprey_relation_overlapping_chunk(const OspreyChunk *a,
                                      const OspreyChunk *b)
{
    int64_t delta;
    RelationSubResult result;
    if (a == NULL || b == NULL || a->size > (uint64_t)INT64_MAX) {
        return false;
    }
    result = relation_sub_checked(&b->address, &a->address, &delta);
    return result == RELATION_SUB_OK && delta >= 0 &&
           delta < (int64_t)a->size;
}

static int cmp_i64_element(gconstpointer ap, gconstpointer bp)
{
    const int64_t *a = ap;
    const int64_t *b = bp;
    return cmp_i64(*a, *b);
}

static int cmp_u64_element(gconstpointer ap, gconstpointer bp)
{
    const uint64_t *a = ap;
    const uint64_t *b = bp;
    return cmp_u64(*a, *b);
}

static int64_t gcd_i64_positive(int64_t a, int64_t b)
{
    while (b != 0) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static uint64_t gcd_u64_positive(uint64_t a, uint64_t b)
{
    while (b != 0) {
        uint64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

bool osprey_relation_addr_difference_gcd(const OspreyAddress *addresses,
                                         size_t count,
                                         const OspreyRegionId *region,
                                         int64_t *out)
{
    GArray *offsets;
    int64_t gcd = 0;
    if (addresses == NULL || region == NULL || out == NULL) return false;

    offsets = g_array_new(FALSE, FALSE, sizeof(int64_t));
    for (size_t i = 0; i < count; i++) {
        if (osprey_relation_same_region(&addresses[i].region, region)) {
            int64_t value = addresses[i].offset;
            g_array_append_val(offsets, value);
        }
    }
    if (offsets->len < 2) {
        g_array_free(offsets, TRUE);
        return false;
    }
    g_array_sort(offsets, cmp_i64_element);

    guint unique = 1;
    for (guint i = 1; i < offsets->len; i++) {
        int64_t previous = g_array_index(offsets, int64_t, unique - 1);
        int64_t current = g_array_index(offsets, int64_t, i);
        if (current == previous) continue;
        g_array_index(offsets, int64_t, unique++) = current;
    }
    if (unique < 2) {
        g_array_free(offsets, TRUE);
        return false;
    }
    for (guint i = 1; i < unique; i++) {
        int64_t previous = g_array_index(offsets, int64_t, i - 1);
        int64_t current = g_array_index(offsets, int64_t, i);
        int64_t difference;
        if (!osprey_check_sub(current, previous, &difference) ||
            difference <= 0) {
            g_array_free(offsets, TRUE);
            return false;
        }
        gcd = gcd == 0 ? difference : gcd_i64_positive(gcd, difference);
    }
    g_array_free(offsets, TRUE);
    if (gcd <= 0) return false;
    *out = gcd;
    return true;
}

bool osprey_relation_size_difference_gcd(const uint64_t *sizes,
                                         size_t count, uint64_t *out)
{
    GArray *values;
    uint64_t gcd = 0;
    if (sizes == NULL || out == NULL) return false;

    values = g_array_new(FALSE, FALSE, sizeof(uint64_t));
    for (size_t i = 0; i < count; i++) {
        if (sizes[i] > (uint64_t)INT64_MAX) {
            g_array_free(values, TRUE);
            return false;
        }
        g_array_append_val(values, sizes[i]);
    }
    if (values->len < 2) {
        g_array_free(values, TRUE);
        return false;
    }
    g_array_sort(values, cmp_u64_element);

    guint unique = 1;
    for (guint i = 1; i < values->len; i++) {
        uint64_t previous = g_array_index(values, uint64_t, unique - 1);
        uint64_t current = g_array_index(values, uint64_t, i);
        if (current == previous) continue;
        g_array_index(values, uint64_t, unique++) = current;
    }
    if (unique < 2) {
        g_array_free(values, TRUE);
        return false;
    }
    for (guint i = 1; i < unique; i++) {
        uint64_t previous = g_array_index(values, uint64_t, i - 1);
        uint64_t current = g_array_index(values, uint64_t, i);
        uint64_t difference = current - previous;
        if (difference == 0) continue;
        gcd = gcd == 0 ? difference : gcd_u64_positive(gcd, difference);
    }
    g_array_free(values, TRUE);
    if (gcd == 0) return false;
    *out = gcd;
    return true;
}

OspreyKey osprey_logical_access_key(uint64_t pc, const OspreyChunk *chunk)
{
    OspreyKey key = osprey_chunk_key(chunk);
    key.tag = 0x4c4143ULL; /* "LAC" */
    key.w[5] = pc;
    return key;
}

bool osprey_logical_access_equal(const OspreyLogicalAccess *a,
                                 const OspreyLogicalAccess *b)
{
    return a != NULL && b != NULL && a->pc == b->pc &&
           relation_chunk_compare(&a->chunk, &b->chunk) == 0;
}

gint osprey_logical_access_compare(gconstpointer ap, gconstpointer bp)
{
    const OspreyLogicalAccess *a = ap;
    const OspreyLogicalAccess *b = bp;
    int c = cmp_u64(a->pc, b->pc);
    if (c != 0) return c;
    return relation_chunk_compare(&a->chunk, &b->chunk);
}

/* ------------------------------------------------------------------ */
/* Relation ownership and indexes                                      */
/* ------------------------------------------------------------------ */

static GArray *relation_array_new(gsize element_size)
{
    return g_array_new(FALSE, FALSE, element_size);
}

static GHashTable *relation_index_new(void)
{
    return g_hash_table_new_full(osprey_key_hash, osprey_key_equal,
                                 osprey_key_free,
                                 (GDestroyNotify)g_array_unref);
}

static void relation_index_add(GHashTable *index, const OspreyKey *key,
                               uint32_t value)
{
    GArray *values = g_hash_table_lookup(index, key);
    if (values == NULL) {
        values = relation_array_new(sizeof(uint32_t));
        g_hash_table_insert(index, osprey_key_new(key), values);
    }
    g_array_append_val(values, value);
}

static OspreyKey alloc_site_key(uint64_t site)
{
    OspreyKey key;
    memset(&key, 0, sizeof(key));
    key.tag = 0x414c53ULL; /* "ALS" */
    key.w[0] = site;
    return key;
}

static OspreyRelations *relations_new(void)
{
    OspreyRelations *relations = g_new0(OspreyRelations, 1);
    relations->logical_accesses = relation_array_new(
        sizeof(OspreyLogicalAccess));
    relations->r01_accessed = relation_array_new(
        sizeof(OspreyInsnChunkRelation));
    relations->r02_accessed = relation_array_new(sizeof(OspreyChunkRelation));
    relations->r03_single_chunk = relation_array_new(
        sizeof(OspreyInsnRegionRelation));
    relations->r04_multi_chunk = relation_array_new(
        sizeof(OspreyInsnRegionRelation));
    relations->r05_high_address = relation_array_new(
        sizeof(OspreyInsnRegionAddressRelation));
    relations->r06_low_address = relation_array_new(
        sizeof(OspreyInsnRegionAddressRelation));
    relations->r07_most_frequent = relation_array_new(
        sizeof(OspreyInsnRegionAddressRelation));
    relations->r08_constant_alloc = relation_array_new(
        sizeof(OspreyAllocRelation));
    relations->r09_alloc_unit = relation_array_new(
        sizeof(OspreyAllocRelation));
    relations->r10_data_flow = relation_array_new(sizeof(OspreyHintRelation));
    relations->r11_unified_access = relation_array_new(
        sizeof(OspreyHintRelation));
    relations->r12_points_to = relation_array_new(sizeof(OspreyHintRelation));
    relations->access_by_pc_region = relation_index_new();
    relations->access_by_chunk = relation_index_new();
    relations->access_by_pc_chunk = relation_index_new();
    relations->alloc_by_site = relation_index_new();
    relations->base_by_address = relation_index_new();
    relations->points_by_chunk = relation_index_new();
    return relations;
}

void osprey_relations_free(OspreyRelations *relations)
{
    if (relations == NULL) return;
#define FREE_ARRAY(_field) do { \
        if (relations->_field != NULL) g_array_free(relations->_field, TRUE); \
    } while (0)
    FREE_ARRAY(logical_accesses);
    FREE_ARRAY(r01_accessed);
    FREE_ARRAY(r02_accessed);
    FREE_ARRAY(r03_single_chunk);
    FREE_ARRAY(r04_multi_chunk);
    FREE_ARRAY(r05_high_address);
    FREE_ARRAY(r06_low_address);
    FREE_ARRAY(r07_most_frequent);
    FREE_ARRAY(r08_constant_alloc);
    FREE_ARRAY(r09_alloc_unit);
    FREE_ARRAY(r10_data_flow);
    FREE_ARRAY(r11_unified_access);
    FREE_ARRAY(r12_points_to);
#undef FREE_ARRAY
    if (relations->access_by_pc_region != NULL) {
        g_hash_table_destroy(relations->access_by_pc_region);
    }
    if (relations->access_by_chunk != NULL) {
        g_hash_table_destroy(relations->access_by_chunk);
    }
    if (relations->access_by_pc_chunk != NULL) {
        g_hash_table_destroy(relations->access_by_pc_chunk);
    }
    if (relations->alloc_by_site != NULL) {
        g_hash_table_destroy(relations->alloc_by_site);
    }
    if (relations->base_by_address != NULL) {
        g_hash_table_destroy(relations->base_by_address);
    }
    if (relations->points_by_chunk != NULL) {
        g_hash_table_destroy(relations->points_by_chunk);
    }
    g_free(relations);
}

static uint32_t sat_add_u32_relation(uint32_t a, uint32_t b)
{
    if (UINT32_MAX - a < b) return UINT32_MAX;
    return a + b;
}

static uint64_t sat_add_u64_relation(uint64_t a, uint64_t b)
{
    if (UINT64_MAX - a < b) return UINT64_MAX;
    return a + b;
}

static bool address_equal_relation(const OspreyAddress *a,
                                   const OspreyAddress *b)
{
    return relation_address_compare(a, b) == 0;
}

static bool chunk_equal_relation(const OspreyChunk *a, const OspreyChunk *b)
{
    return relation_chunk_compare(a, b) == 0;
}

static int cmp_insn_chunk_relation(gconstpointer ap, gconstpointer bp)
{
    const OspreyInsnChunkRelation *a = ap;
    const OspreyInsnChunkRelation *b = bp;
    int c = cmp_u64(a->pc, b->pc);
    if (c != 0) return c;
    return relation_chunk_compare(&a->chunk, &b->chunk);
}

static int cmp_chunk_relation(gconstpointer ap, gconstpointer bp)
{
    const OspreyChunkRelation *a = ap;
    const OspreyChunkRelation *b = bp;
    return relation_chunk_compare(&a->chunk, &b->chunk);
}

static int cmp_insn_region_relation(gconstpointer ap, gconstpointer bp)
{
    const OspreyInsnRegionRelation *a = ap;
    const OspreyInsnRegionRelation *b = bp;
    int c = cmp_u64(a->pc, b->pc);
    if (c != 0) return c;
    return relation_region_compare(&a->region, &b->region);
}

static int cmp_insn_region_address_relation(gconstpointer ap,
                                            gconstpointer bp)
{
    const OspreyInsnRegionAddressRelation *a = ap;
    const OspreyInsnRegionAddressRelation *b = bp;
    int c = cmp_u64(a->pc, b->pc);
    if (c != 0) return c;
    c = relation_region_compare(&a->region, &b->region);
    if (c != 0) return c;
    c = relation_address_compare(&a->address, &b->address);
    if (c != 0) return c;
    return cmp_u64(a->count, b->count);
}

static int cmp_alloc_relation(gconstpointer ap, gconstpointer bp)
{
    const OspreyAllocRelation *a = ap;
    const OspreyAllocRelation *b = bp;
    int c = cmp_u64(a->site_pc, b->site_pc);
    if (c != 0) return c;
    return cmp_u64(a->size, b->size);
}

static int cmp_hint_relation(gconstpointer ap, gconstpointer bp)
{
    const OspreyHintRelation *a = ap;
    const OspreyHintRelation *b = bp;
    int c = cmp_u64(a->kind, b->kind);
    if (c != 0) return c;
    c = relation_address_compare(&a->a1, &b->a1);
    if (c != 0) return c;
    c = relation_address_compare(&a->a2, &b->a2);
    if (c != 0) return c;
    return cmp_i64(a->size, b->size);
}

/* ------------------------------------------------------------------ */
/* Logical source normalization and H07                                */
/* ------------------------------------------------------------------ */

static void copy_logical_accesses(const OspreyContext *ctx,
                                  OspreyRelations *relations)
{
    GArray *sorted = g_array_new(FALSE, FALSE, sizeof(OspreyLogicalAccess));
    for (guint i = 0; ctx->logical_access_facts != NULL &&
                       i < ctx->logical_access_facts->len; i++) {
        OspreyLogicalAccess row = g_array_index(
            ctx->logical_access_facts, OspreyLogicalAccess, i);
        g_array_append_val(sorted, row);
    }
    g_array_sort(sorted, osprey_logical_access_compare);
    for (guint i = 0; i < sorted->len; i++) {
        OspreyLogicalAccess row = g_array_index(sorted, OspreyLogicalAccess, i);
        guint last = relations->logical_accesses->len;
        if (last != 0) {
            OspreyLogicalAccess *previous = &g_array_index(
                relations->logical_accesses, OspreyLogicalAccess, last - 1);
            if (osprey_logical_access_equal(previous, &row)) {
                previous->dynamic_count = sat_add_u32_relation(
                    previous->dynamic_count, row.dynamic_count);
                previous->sample_support = sat_add_u32_relation(
                    previous->sample_support, row.sample_support);
                continue;
            }
        }
        g_array_append_val(relations->logical_accesses, row);
    }
    g_array_free(sorted, TRUE);
}

static void build_r01_r02(OspreyRelations *relations)
{
    GArray *chunks = g_array_new(FALSE, FALSE, sizeof(OspreyChunkRelation));
    for (guint i = 0; i < relations->logical_accesses->len; i++) {
        const OspreyLogicalAccess *logical = &g_array_index(
            relations->logical_accesses, OspreyLogicalAccess, i);
        OspreyInsnChunkRelation r01;
        memset(&r01, 0, sizeof(r01));
        r01.pc = logical->pc;
        r01.chunk = logical->chunk;
        g_array_append_val(relations->r01_accessed, r01);

        OspreyChunkRelation r02;
        memset(&r02, 0, sizeof(r02));
        r02.chunk = logical->chunk;
        g_array_append_val(chunks, r02);
    }
    g_array_sort(relations->r01_accessed, cmp_insn_chunk_relation);
    g_array_sort(chunks, cmp_chunk_relation);
    for (guint i = 0; i < chunks->len; i++) {
        const OspreyChunkRelation *row = &g_array_index(
            chunks, OspreyChunkRelation, i);
        if (relations->r02_accessed->len != 0 &&
            chunk_equal_relation(&row->chunk, &g_array_index(
                relations->r02_accessed, OspreyChunkRelation,
                relations->r02_accessed->len - 1).chunk)) {
            continue;
        }
        g_array_append_val(relations->r02_accessed, *row);
    }
    g_array_free(chunks, TRUE);
}

static bool same_pc_region_logical(const OspreyLogicalAccess *a,
                                   const OspreyLogicalAccess *b)
{
    return a->pc == b->pc && osprey_relation_same_region(
        &a->chunk.address.region, &b->chunk.address.region);
}

static void build_r03_r07(OspreyRelations *relations)
{
    guint i = 0;
    while (i < relations->logical_accesses->len) {
        const OspreyLogicalAccess *first = &g_array_index(
            relations->logical_accesses, OspreyLogicalAccess, i);
        guint end = i + 1;
        while (end < relations->logical_accesses->len &&
               same_pc_region_logical(first, &g_array_index(
                   relations->logical_accesses, OspreyLogicalAccess, end))) {
            end++;
        }

        OspreyInsnRegionRelation region_relation;
        memset(&region_relation, 0, sizeof(region_relation));
        region_relation.pc = first->pc;
        region_relation.region = first->chunk.address.region;
        if (end - i == 1) {
            g_array_append_val(relations->r03_single_chunk, region_relation);
        } else {
            g_array_append_val(relations->r04_multi_chunk, region_relation);
        }

        const OspreyLogicalAccess *low = first;
        const OspreyLogicalAccess *high = first;
        uint32_t maximum_count = first->dynamic_count;
        for (guint j = i + 1; j < end; j++) {
            const OspreyLogicalAccess *row = &g_array_index(
                relations->logical_accesses, OspreyLogicalAccess, j);
            if (row->chunk.address.offset < low->chunk.address.offset) {
                low = row;
            }
            if (row->chunk.address.offset > high->chunk.address.offset) {
                high = row;
            }
            if (row->dynamic_count > maximum_count) {
                maximum_count = row->dynamic_count;
            }
        }

        OspreyInsnRegionAddressRelation extrema;
        memset(&extrema, 0, sizeof(extrema));
        extrema.pc = first->pc;
        extrema.region = first->chunk.address.region;
        extrema.address = high->chunk.address;
        g_array_append_val(relations->r05_high_address, extrema);
        extrema.address = low->chunk.address;
        g_array_append_val(relations->r06_low_address, extrema);

        /* H07 groups widths at one address.  An address is a R07 result
         * when the maximum count of its widths equals the group maximum. */
        for (guint j = i; j < end; ) {
            const OspreyLogicalAccess *row = &g_array_index(
                relations->logical_accesses, OspreyLogicalAccess, j);
            int64_t offset = row->chunk.address.offset;
            uint32_t address_count = row->dynamic_count;
            guint next = j + 1;
            while (next < end &&
                   g_array_index(relations->logical_accesses,
                                 OspreyLogicalAccess, next)
                       .chunk.address.offset == offset) {
                const OspreyLogicalAccess *same_address = &g_array_index(
                    relations->logical_accesses, OspreyLogicalAccess, next);
                if (same_address->dynamic_count > address_count) {
                    address_count = same_address->dynamic_count;
                }
                next++;
            }
            if (address_count == maximum_count) {
                OspreyInsnRegionAddressRelation most;
                memset(&most, 0, sizeof(most));
                most.pc = first->pc;
                most.region = first->chunk.address.region;
                most.address = row->chunk.address;
                most.count = address_count;
                g_array_append_val(relations->r07_most_frequent, most);
            }
            j = next;
        }
        i = end;
    }
    g_array_sort(relations->r03_single_chunk, cmp_insn_region_relation);
    g_array_sort(relations->r04_multi_chunk, cmp_insn_region_relation);
    g_array_sort(relations->r05_high_address,
                 cmp_insn_region_address_relation);
    g_array_sort(relations->r06_low_address,
                 cmp_insn_region_address_relation);
    g_array_sort(relations->r07_most_frequent,
                 cmp_insn_region_address_relation);
}

/* ------------------------------------------------------------------ */
/* R08/R09 allocation relations                                        */
/* ------------------------------------------------------------------ */

static bool build_r08_r09(const OspreyContext *ctx, OspreyRelations *relations)
{
    GArray *allocs = g_array_new(FALSE, FALSE, sizeof(OspreyAllocRelation));
    for (guint i = 0; i < ctx->alloc_facts->len; i++) {
        const OspreyMallocFact *fact = &g_array_index(
            ctx->alloc_facts, OspreyMallocFact, i);
        if (fact->requested_size > (uint64_t)INT64_MAX) {
            g_array_free(allocs, TRUE);
            return false;
        }
        OspreyAllocRelation row;
        row.site_pc = fact->site_pc;
        row.size = fact->requested_size;
        g_array_append_val(allocs, row);
    }
    g_array_sort(allocs, cmp_alloc_relation);

    guint i = 0;
    while (i < allocs->len) {
        OspreyAllocRelation *first = &g_array_index(
            allocs, OspreyAllocRelation, i);
        guint end = i + 1;
        while (end < allocs->len &&
               g_array_index(allocs, OspreyAllocRelation, end).site_pc ==
                   first->site_pc) {
            end++;
        }
        guint unique = i;
        for (guint j = i; j < end; j++) {
            OspreyAllocRelation row = g_array_index(allocs,
                                                    OspreyAllocRelation, j);
            if (unique != i &&
                g_array_index(allocs, OspreyAllocRelation, unique - 1).size ==
                    row.size) {
                continue;
            }
            g_array_index(allocs, OspreyAllocRelation, unique++) = row;
        }
        if (unique - i == 1) {
            OspreyAllocRelation row = g_array_index(allocs,
                                                    OspreyAllocRelation, i);
            g_array_append_val(relations->r08_constant_alloc, row);
        } else if (unique - i >= 2) {
            uint64_t gcd = 0;
            for (guint j = i + 1; j < unique; j++) {
                uint64_t previous = g_array_index(
                    allocs, OspreyAllocRelation, j - 1).size;
                uint64_t current = g_array_index(
                    allocs, OspreyAllocRelation, j).size;
                uint64_t difference = current - previous;
                gcd = gcd == 0 ? difference : gcd_u64_positive(gcd, difference);
            }
            if (gcd == 0) {
                g_array_free(allocs, TRUE);
                return false;
            }
            OspreyAllocRelation row;
            row.site_pc = first->site_pc;
            row.size = gcd;
            g_array_append_val(relations->r09_alloc_unit, row);
        }
        i = end;
    }
    g_array_sort(relations->r08_constant_alloc, cmp_alloc_relation);
    g_array_sort(relations->r09_alloc_unit, cmp_alloc_relation);
    g_array_free(allocs, TRUE);
    return true;
}

/* ------------------------------------------------------------------ */
/* Hint relation helpers and R10                                        */
/* ------------------------------------------------------------------ */

static void hint_relation_add(GArray *hints, const OspreyAddress *a1,
                              const OspreyAddress *a2, int64_t size,
                              uint8_t kind)
{
    for (guint i = 0; i < hints->len; i++) {
        OspreyHintRelation *existing = &g_array_index(
            hints, OspreyHintRelation, i);
        if (existing->kind == kind && existing->size == size &&
            address_equal_relation(&existing->a1, a1) &&
            address_equal_relation(&existing->a2, a2)) {
            existing->witness_count = sat_add_u64_relation(
                existing->witness_count, 1);
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

typedef struct RelationCopyEntry {
    OspreyCopyFact fact;
} RelationCopyEntry;

static int cmp_copy_entry(gconstpointer ap, gconstpointer bp)
{
    const RelationCopyEntry *a = ap;
    const RelationCopyEntry *b = bp;
    int c = relation_region_compare(&a->fact.source.address.region,
                                    &b->fact.source.address.region);
    if (c != 0) return c;
    c = relation_region_compare(&a->fact.destination.address.region,
                                &b->fact.destination.address.region);
    if (c != 0) return c;
    c = relation_address_compare(&a->fact.source.address,
                                 &b->fact.source.address);
    if (c != 0) return c;
    c = cmp_u64(a->fact.source.size, b->fact.source.size);
    if (c != 0) return c;
    c = relation_address_compare(&a->fact.destination.address,
                                 &b->fact.destination.address);
    if (c != 0) return c;
    return cmp_u64(a->fact.destination.size, b->fact.destination.size);
}

static bool same_copy_bucket(const RelationCopyEntry *a,
                             const RelationCopyEntry *b)
{
    return osprey_relation_same_region(&a->fact.source.address.region,
                                       &b->fact.source.address.region) &&
           osprey_relation_same_region(&a->fact.destination.address.region,
                                       &b->fact.destination.address.region);
}

static bool build_r10(const OspreyContext *ctx, OspreyRelations *relations)
{
    GArray *copies = g_array_new(FALSE, FALSE, sizeof(RelationCopyEntry));
    for (guint i = 0; i < ctx->copy_facts->len; i++) {
        RelationCopyEntry entry;
        entry.fact = g_array_index(ctx->copy_facts, OspreyCopyFact, i);
        g_array_append_val(copies, entry);
    }
    g_array_sort(copies, cmp_copy_entry);
    /* F03 identity is the complete source/destination chunk pair.  A
     * repeated equality-equivalent row is one fact, not another R10
     * witness; compact it before forming fact pairs. */
    guint unique = 0;
    for (guint i = 0; i < copies->len; i++) {
        RelationCopyEntry entry = g_array_index(copies, RelationCopyEntry, i);
        if (unique != 0 && cmp_copy_entry(
                &entry, &g_array_index(copies, RelationCopyEntry,
                                       unique - 1)) == 0) {
            continue;
        }
        g_array_index(copies, RelationCopyEntry, unique++) = entry;
    }
    g_array_set_size(copies, unique);

    guint bucket_start = 0;
    while (bucket_start < copies->len) {
        const RelationCopyEntry *bucket_first = &g_array_index(
            copies, RelationCopyEntry, bucket_start);
        guint bucket_end = bucket_start + 1;
        while (bucket_end < copies->len &&
               same_copy_bucket(bucket_first, &g_array_index(
                   copies, RelationCopyEntry, bucket_end))) {
            bucket_end++;
        }

        /* The source-address ordering makes every nonzero source delta
         * positive, so the emitted source/destination roles stay anchored
         * to the first copy in the pair. */
        for (guint i = bucket_start; i < bucket_end; i++) {
            const RelationCopyEntry *first = &g_array_index(
                copies, RelationCopyEntry, i);
            for (guint j = i + 1; j < bucket_end; j++) {
                const RelationCopyEntry *second = &g_array_index(
                    copies, RelationCopyEntry, j);
                int64_t source_delta;
                int64_t destination_delta;
                RelationSubResult source_result = relation_sub_checked(
                    &second->fact.source.address,
                    &first->fact.source.address, &source_delta);
                if (source_result == RELATION_SUB_OVERFLOW) {
                    g_array_free(copies, TRUE);
                    return false;
                }
                if (source_result != RELATION_SUB_OK) continue;
                RelationSubResult destination_result = relation_sub_checked(
                    &second->fact.destination.address,
                    &first->fact.destination.address, &destination_delta);
                if (destination_result == RELATION_SUB_OVERFLOW) {
                    g_array_free(copies, TRUE);
                    return false;
                }
                if (destination_result != RELATION_SUB_OK ||
                    source_delta <= 0 || source_delta != destination_delta) {
                    continue;
                }
                hint_relation_add(relations->r10_data_flow,
                                  &first->fact.source.address,
                                  &first->fact.destination.address,
                                  source_delta,
                                  OSPREY_RELATION_DATA_FLOW);
            }
        }
        bucket_start = bucket_end;
    }
    g_array_sort(relations->r10_data_flow, cmp_hint_relation);
    g_array_free(copies, TRUE);
    return true;
}

/* ------------------------------------------------------------------ */
/* R11 unified-access relations                                        */
/* ------------------------------------------------------------------ */

typedef struct RelationAccessPair {
    uint64_t pc;
    OspreyChunk first;
    OspreyChunk second;
    __int128 skew;
} RelationAccessPair;

static int cmp_i128(__int128 a, __int128 b)
{
    return a < b ? -1 : a != b;
}

static int cmp_access_pair(gconstpointer ap, gconstpointer bp)
{
    const RelationAccessPair *a = ap;
    const RelationAccessPair *b = bp;
    int c = relation_region_compare(&a->first.address.region,
                                    &b->first.address.region);
    if (c != 0) return c;
    c = relation_region_compare(&a->second.address.region,
                                &b->second.address.region);
    if (c != 0) return c;
    c = cmp_i128(a->skew, b->skew);
    if (c != 0) return c;
    c = cmp_u64(a->pc, b->pc);
    if (c != 0) return c;
    c = relation_chunk_compare(&a->first, &b->first);
    if (c != 0) return c;
    return relation_chunk_compare(&a->second, &b->second);
}

static bool same_access_pair_group(const RelationAccessPair *a,
                                   const RelationAccessPair *b)
{
    return osprey_relation_same_region(&a->first.address.region,
                                       &b->first.address.region) &&
           osprey_relation_same_region(&a->second.address.region,
                                       &b->second.address.region) &&
           a->skew == b->skew;
}

static bool build_access_pairs(const OspreyRelations *relations,
                               GArray *pairs)
{
    for (guint i = 0; i < relations->r01_accessed->len; i++) {
        const OspreyInsnChunkRelation *first = &g_array_index(
            relations->r01_accessed, OspreyInsnChunkRelation, i);
        for (guint j = i + 1; j < relations->r01_accessed->len; j++) {
            const OspreyInsnChunkRelation *second = &g_array_index(
                relations->r01_accessed, OspreyInsnChunkRelation, j);
            if (first->pc != second->pc) break;
            if (chunk_equal_relation(&first->chunk, &second->chunk)) continue;
            RelationAccessPair pair;
            memset(&pair, 0, sizeof(pair));
            pair.pc = first->pc;
            if (relation_chunk_compare(&first->chunk, &second->chunk) < 0) {
                pair.first = first->chunk;
                pair.second = second->chunk;
            } else {
                pair.first = second->chunk;
                pair.second = first->chunk;
            }
            pair.skew = (__int128)pair.first.address.offset -
                        (__int128)pair.second.address.offset;
            g_array_append_val(pairs, pair);
        }
    }
    g_array_sort(pairs, cmp_access_pair);
    return true;
}

static bool build_r11(const OspreyRelations *relations)
{
    GArray *pairs = g_array_new(FALSE, FALSE, sizeof(RelationAccessPair));
    if (!build_access_pairs(relations, pairs)) {
        g_array_free(pairs, TRUE);
        return false;
    }
    guint group_start = 0;
    while (group_start < pairs->len) {
        const RelationAccessPair *group_first = &g_array_index(
            pairs, RelationAccessPair, group_start);
        guint group_end = group_start + 1;
        while (group_end < pairs->len &&
               same_access_pair_group(group_first, &g_array_index(
                   pairs, RelationAccessPair, group_end))) {
            group_end++;
        }
        for (guint i = group_start; i < group_end; i++) {
            const RelationAccessPair *first = &g_array_index(
                pairs, RelationAccessPair, i);
            for (guint j = i + 1; j < group_end; j++) {
                const RelationAccessPair *second = &g_array_index(
                    pairs, RelationAccessPair, j);
                if (first->pc == second->pc) continue;
                int64_t first_delta;
                int64_t second_delta;
                RelationSubResult first_result = relation_sub_checked(
                    &second->first.address, &first->first.address,
                    &first_delta);
                if (first_result == RELATION_SUB_OVERFLOW) {
                    g_array_free(pairs, TRUE);
                    return false;
                }
                if (first_result != RELATION_SUB_OK) continue;
                RelationSubResult second_result = relation_sub_checked(
                    &second->second.address, &first->second.address,
                    &second_delta);
                if (second_result == RELATION_SUB_OVERFLOW) {
                    g_array_free(pairs, TRUE);
                    return false;
                }
                if (second_result != RELATION_SUB_OK ||
                    first_delta != second_delta || first_delta == 0) {
                    continue;
                }
                if (first_delta > 0) {
                    hint_relation_add(relations->r11_unified_access,
                                      &first->first.address,
                                      &first->second.address, first_delta,
                                      OSPREY_RELATION_UNIFIED_ACCESS);
                } else {
                    /* Negating INT64_MIN is itself not representable. */
                    if (first_delta == INT64_MIN ||
                        second_delta == INT64_MIN) {
                        g_array_free(pairs, TRUE);
                        return false;
                    }
                    int64_t reverse_delta = -first_delta;
                    if (reverse_delta <= 0) continue;
                    hint_relation_add(relations->r11_unified_access,
                                      &second->first.address,
                                      &second->second.address, reverse_delta,
                                      OSPREY_RELATION_UNIFIED_ACCESS);
                }
            }
        }
        group_start = group_end;
    }
    g_array_sort(relations->r11_unified_access, cmp_hint_relation);
    g_array_free(pairs, TRUE);
    return true;
}

/* ------------------------------------------------------------------ */
/* R12 points-to relations                                             */
/* ------------------------------------------------------------------ */

typedef struct RelationBaseEntry {
    OspreyAddress base;
    OspreyChunk chunk;
} RelationBaseEntry;

typedef struct RelationPointEntry {
    OspreyChunk pointer_chunk;
    OspreyAddress target;
} RelationPointEntry;

static int cmp_base_entry(gconstpointer ap, gconstpointer bp)
{
    const RelationBaseEntry *a = ap;
    const RelationBaseEntry *b = bp;
    int c = relation_address_compare(&a->base, &b->base);
    if (c != 0) return c;
    return relation_chunk_compare(&a->chunk, &b->chunk);
}

static int cmp_point_entry(gconstpointer ap, gconstpointer bp)
{
    const RelationPointEntry *a = ap;
    const RelationPointEntry *b = bp;
    int c = relation_chunk_compare(&a->pointer_chunk, &b->pointer_chunk);
    if (c != 0) return c;
    return relation_address_compare(&a->target, &b->target);
}

static bool r02_contains(const OspreyRelations *relations,
                         const OspreyChunk *chunk)
{
    guint low = 0;
    guint high = relations->r02_accessed->len;
    while (low < high) {
        guint middle = low + (high - low) / 2;
        const OspreyChunkRelation *row = &g_array_index(
            relations->r02_accessed, OspreyChunkRelation, middle);
        int c = relation_chunk_compare(&row->chunk, chunk);
        if (c == 0) return true;
        if (c < 0) low = middle + 1;
        else high = middle;
    }
    return false;
}

static guint base_lower_bound(const GArray *bases,
                              const OspreyAddress *base)
{
    guint low = 0;
    guint high = bases->len;
    while (low < high) {
        guint middle = low + (high - low) / 2;
        const RelationBaseEntry *entry = &g_array_index(
            bases, RelationBaseEntry, middle);
        if (relation_address_compare(&entry->base, base) < 0) {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    return low;
}

static guint base_upper_bound(const GArray *bases,
                              const OspreyAddress *base)
{
    guint low = 0;
    guint high = bases->len;
    while (low < high) {
        guint middle = low + (high - low) / 2;
        const RelationBaseEntry *entry = &g_array_index(
            bases, RelationBaseEntry, middle);
        if (relation_address_compare(&entry->base, base) <= 0) {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    return low;
}

static bool build_r12(const OspreyContext *ctx, OspreyRelations *relations)
{
    GArray *bases = g_array_new(FALSE, FALSE, sizeof(RelationBaseEntry));
    GArray *points = g_array_new(FALSE, FALSE, sizeof(RelationPointEntry));

    for (guint i = 0; i < ctx->base_facts->len; i++) {
        const OspreyBaseFact *fact = &g_array_index(
            ctx->base_facts, OspreyBaseFact, i);
        if (!r02_contains(relations, &fact->chunk)) continue;
        RelationBaseEntry entry;
        entry.base = fact->base;
        entry.chunk = fact->chunk;
        g_array_append_val(bases, entry);
    }
    g_array_sort(bases, cmp_base_entry);

    guint unique_bases = 0;
    for (guint i = 0; i < bases->len; i++) {
        RelationBaseEntry entry = g_array_index(bases, RelationBaseEntry, i);
        if (unique_bases != 0 &&
            cmp_base_entry(&entry, &g_array_index(
                bases, RelationBaseEntry, unique_bases - 1)) == 0) {
            continue;
        }
        g_array_index(bases, RelationBaseEntry, unique_bases++) = entry;
    }
    g_array_set_size(bases, unique_bases);

    for (guint i = 0; i < ctx->points_facts->len; i++) {
        const OspreyPointsToFact *fact = &g_array_index(
            ctx->points_facts, OspreyPointsToFact, i);
        RelationPointEntry entry;
        entry.pointer_chunk = fact->pointer_chunk;
        entry.target = fact->target;
        g_array_append_val(points, entry);
    }
    g_array_sort(points, cmp_point_entry);
    guint unique_points = 0;
    for (guint i = 0; i < points->len; i++) {
        RelationPointEntry entry = g_array_index(points, RelationPointEntry, i);
        if (unique_points != 0 &&
            cmp_point_entry(&entry, &g_array_index(
                points, RelationPointEntry, unique_points - 1)) == 0) {
            continue;
        }
        g_array_index(points, RelationPointEntry, unique_points++) = entry;
    }
    g_array_set_size(points, unique_points);

    guint i = 0;
    while (i < points->len) {
        const RelationPointEntry *first = &g_array_index(
            points, RelationPointEntry, i);
        guint end = i + 1;
        while (end < points->len &&
               chunk_equal_relation(&first->pointer_chunk,
                                    &g_array_index(points, RelationPointEntry,
                                                   end).pointer_chunk)) {
            end++;
        }
        for (guint a = i; a < end; a++) {
            for (guint b = a + 1; b < end; b++) {
                OspreyAddress target1 = g_array_index(
                    points, RelationPointEntry, a).target;
                OspreyAddress target2 = g_array_index(
                    points, RelationPointEntry, b).target;
                if (address_equal_relation(&target1, &target2)) continue;
                if (relation_address_compare(&target1, &target2) > 0) {
                    OspreyAddress swap = target1;
                    target1 = target2;
                    target2 = swap;
                }

                guint source_begin = base_lower_bound(bases, &target1);
                guint source_end = base_upper_bound(bases, &target1);
                guint destination_begin = base_lower_bound(bases, &target2);
                guint destination_end = base_upper_bound(bases, &target2);
                for (guint bs = source_begin; bs < source_end; bs++) {
                    const RelationBaseEntry *source = &g_array_index(
                        bases, RelationBaseEntry, bs);
                    if (!osprey_relation_same_region(
                            &source->chunk.address.region,
                            &target1.region)) {
                        continue;
                    }
                    int64_t source_delta;
                    RelationSubResult source_result = relation_sub_checked(
                        &source->chunk.address, &target1, &source_delta);
                    if (source_result == RELATION_SUB_OVERFLOW) {
                        g_array_free(bases, TRUE);
                        g_array_free(points, TRUE);
                        return false;
                    }
                    if (source_result != RELATION_SUB_OK || source_delta <= 0) {
                        continue;
                    }
                    for (guint bd = destination_begin; bd < destination_end;
                         bd++) {
                        const RelationBaseEntry *destination = &g_array_index(
                            bases, RelationBaseEntry, bd);
                        if (!osprey_relation_same_region(
                                &destination->chunk.address.region,
                                &target2.region)) {
                            continue;
                        }
                        int64_t destination_delta;
                        RelationSubResult destination_result =
                            relation_sub_checked(&destination->chunk.address,
                                                 &target2,
                                                 &destination_delta);
                        if (destination_result == RELATION_SUB_OVERFLOW) {
                            g_array_free(bases, TRUE);
                            g_array_free(points, TRUE);
                            return false;
                        }
                        if (destination_result == RELATION_SUB_OK &&
                            destination_delta == source_delta) {
                            hint_relation_add(relations->r12_points_to,
                                              &target1, &target2,
                                              source_delta,
                                              OSPREY_RELATION_POINTS_TO);
                        }
                    }
                }
            }
        }
        i = end;
    }
    g_array_sort(relations->r12_points_to, cmp_hint_relation);
    g_array_free(bases, TRUE);
    g_array_free(points, TRUE);
    return true;
}

/* ------------------------------------------------------------------ */
/* Index construction and public build                                 */
/* ------------------------------------------------------------------ */

static void build_indexes(const OspreyContext *ctx, OspreyRelations *relations)
{
    for (guint i = 0; i < relations->r01_accessed->len; i++) {
        const OspreyInsnChunkRelation *row = &g_array_index(
            relations->r01_accessed, OspreyInsnChunkRelation, i);
        OspreyKey pc_region = osprey_pc_region_key(
            row->pc, &row->chunk.address.region);
        OspreyKey chunk = osprey_chunk_key(&row->chunk);
        OspreyKey pc_chunk = osprey_logical_access_key(row->pc, &row->chunk);
        relation_index_add(relations->access_by_pc_region, &pc_region, i);
        relation_index_add(relations->access_by_chunk, &chunk, i);
        relation_index_add(relations->access_by_pc_chunk, &pc_chunk, i);
    }
    for (guint i = 0; i < ctx->alloc_facts->len; i++) {
        const OspreyMallocFact *row = &g_array_index(
            ctx->alloc_facts, OspreyMallocFact, i);
        OspreyKey key = alloc_site_key(row->site_pc);
        relation_index_add(relations->alloc_by_site, &key, i);
    }
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        const OspreyBaseFact *row = &g_array_index(
            ctx->base_facts, OspreyBaseFact, i);
        OspreyKey key = osprey_addr_key(&row->base);
        relation_index_add(relations->base_by_address, &key, i);
    }
    for (guint i = 0; i < ctx->points_facts->len; i++) {
        const OspreyPointsToFact *row = &g_array_index(
            ctx->points_facts, OspreyPointsToFact, i);
        OspreyKey key = osprey_chunk_key(&row->pointer_chunk);
        relation_index_add(relations->points_by_chunk, &key, i);
    }
}

OspreyStatus osprey_relations_build(OspreyContext *ctx)
{
    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    OspreyRelations *relations = relations_new();
    copy_logical_accesses(ctx, relations);
    build_r01_r02(relations);
    build_r03_r07(relations);
    if (!build_r08_r09(ctx, relations) || !build_r10(ctx, relations) ||
        !build_r11(relations) || !build_r12(ctx, relations)) {
        osprey_relations_free(relations);
        return OSPREY_RELATION_ARITHMETIC;
    }
    build_indexes(ctx, relations);

    OspreyRelations *old = ctx->relations;
    ctx->relations = relations;
    osprey_relations_free(old);
    return OSPREY_OK;
}

/* ------------------------------------------------------------------ */
/* Canonical relation dump                                              */
/* ------------------------------------------------------------------ */

static void dump_region(FILE *out, const OspreyRegionId *region)
{
    fprintf(out, "%u %" PRIu64 " %" PRIu64,
            (unsigned)region->kind, region->code_image_id,
            region->site_offset);
}

static void dump_address(FILE *out, const OspreyAddress *address)
{
    dump_region(out, &address->region);
    fprintf(out, " %" PRId64, address->offset);
}

void osprey_relations_dump(const OspreyRelations *relations, FILE *out)
{
    if (relations == NULL || out == NULL) return;
    for (guint i = 0; i < relations->r01_accessed->len; i++) {
        const OspreyInsnChunkRelation *r = &g_array_index(
            relations->r01_accessed, OspreyInsnChunkRelation, i);
        fprintf(out, "R01 %" PRIu64 " ", r->pc);
        dump_address(out, &r->chunk.address);
        fprintf(out, " %" PRIu64 "\n", r->chunk.size);
    }
    for (guint i = 0; i < relations->r02_accessed->len; i++) {
        const OspreyChunkRelation *r = &g_array_index(
            relations->r02_accessed, OspreyChunkRelation, i);
        fprintf(out, "R02 ");
        dump_address(out, &r->chunk.address);
        fprintf(out, " %" PRIu64 "\n", r->chunk.size);
    }
#define DUMP_REGION_REL(_name, _field) do { \
    for (guint i = 0; i < relations->_field->len; i++) { \
        const OspreyInsnRegionRelation *r = &g_array_index( \
            relations->_field, OspreyInsnRegionRelation, i); \
        fprintf(out, _name " %" PRIu64 " ", r->pc); \
        dump_region(out, &r->region); \
        fputc('\n', out); \
    } \
} while (0)
    DUMP_REGION_REL("R03", r03_single_chunk);
    DUMP_REGION_REL("R04", r04_multi_chunk);
#undef DUMP_REGION_REL
#define DUMP_REGION_ADDRESS_REL(_name, _field) do { \
    for (guint i = 0; i < relations->_field->len; i++) { \
        const OspreyInsnRegionAddressRelation *r = &g_array_index( \
            relations->_field, OspreyInsnRegionAddressRelation, i); \
        fprintf(out, _name " %" PRIu64 " ", r->pc); \
        dump_region(out, &r->region); \
        fputs(" ", out); \
        dump_address(out, &r->address); \
        fprintf(out, " %" PRIu32 "\n", r->count); \
    } \
} while (0)
    DUMP_REGION_ADDRESS_REL("R05", r05_high_address);
    DUMP_REGION_ADDRESS_REL("R06", r06_low_address);
    DUMP_REGION_ADDRESS_REL("R07", r07_most_frequent);
#undef DUMP_REGION_ADDRESS_REL
#define DUMP_ALLOC_REL(_name, _field) do { \
    for (guint i = 0; i < relations->_field->len; i++) { \
        const OspreyAllocRelation *r = &g_array_index( \
            relations->_field, OspreyAllocRelation, i); \
        fprintf(out, _name " %" PRIu64 " %" PRIu64 "\n", \
                r->site_pc, r->size); \
    } \
} while (0)
    DUMP_ALLOC_REL("R08", r08_constant_alloc);
    DUMP_ALLOC_REL("R09", r09_alloc_unit);
#undef DUMP_ALLOC_REL
#define DUMP_HINT_REL(_name, _field) do { \
    for (guint i = 0; i < relations->_field->len; i++) { \
        const OspreyHintRelation *r = &g_array_index( \
            relations->_field, OspreyHintRelation, i); \
        fputs(_name " ", out); \
        dump_address(out, &r->a1); \
        fputs(" ", out); \
        dump_address(out, &r->a2); \
        fprintf(out, " %" PRId64 " %" PRIu64 "\n", \
                r->size, r->witness_count); \
    } \
} while (0)
    DUMP_HINT_REL("R10", r10_data_flow);
    DUMP_HINT_REL("R11", r11_unified_access);
    DUMP_HINT_REL("R12", r12_points_to);
#undef DUMP_HINT_REL
}
