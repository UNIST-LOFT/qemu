/* Stage 3.1 deterministic relation and logical-Access tests. */

#include "osprey.h"
#include "osprey-internal.h"

#include <inttypes.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

bool stage3_reference_build(const OspreyContext *ctx, OspreyRelations **out);

static unsigned failures;
static unsigned registered;
static unsigned executed;

#define CHECK(_condition, _message) do {                                  \
    if (!(_condition)) {                                                   \
        fprintf(stderr, "FAIL: %s (line %d)\n", (_message), __LINE__); \
        failures++;                                                        \
    }                                                                         \
} while (0)

static OspreyConfig relation_config(void)
{
    OspreyConfig config;
    memset(&config, 0, sizeof(config));
    config.enabled = true;
    config.shared_bytes = 1u << 20;
    config.max_facts = 262144;
    config.max_chunks_per_region = 8192;
    config.max_candidates_per_kind_region = 4096;
    config.max_variables = 100000;
    config.max_factors = 500000;
    config.max_exact_clique_vars = 20;
    config.report_threshold = 0.2;
    return config;
}

static OspreyRegionId make_region(OspreyRegionKind kind, uint64_t site)
{
    OspreyRegionId region;
    memset(&region, 0, sizeof(region));
    region.kind = kind;
    region.site_offset = site;
    return region;
}

static OspreyAddress make_address(OspreyRegionId region, int64_t offset)
{
    OspreyAddress address;
    memset(&address, 0, sizeof(address));
    address.region = region;
    address.offset = offset;
    return address;
}

static OspreyChunk make_chunk(OspreyRegionId region, int64_t offset,
                              uint64_t size)
{
    OspreyChunk chunk;
    memset(&chunk, 0, sizeof(chunk));
    chunk.address = make_address(region, offset);
    chunk.size = size;
    return chunk;
}

static void add_copy(OspreyContext *ctx, OspreyRegionId source_region,
                     int64_t source_offset, uint64_t source_size,
                     OspreyRegionId destination_region,
                     int64_t destination_offset, uint64_t destination_size)
{
    OspreyCopyFact row;
    memset(&row, 0, sizeof(row));
    row.source = make_chunk(source_region, source_offset, source_size);
    row.destination = make_chunk(destination_region, destination_offset,
                                 destination_size);
    row.sample_support = 1;
    g_array_append_val(ctx->copy_facts, row);
}

static void add_base(OspreyContext *ctx, OspreyRegionId chunk_region,
                     int64_t chunk_offset, uint64_t chunk_size,
                     OspreyAddress base)
{
    OspreyBaseFact row;
    memset(&row, 0, sizeof(row));
    row.chunk = make_chunk(chunk_region, chunk_offset, chunk_size);
    row.base = base;
    row.sample_support = 1;
    g_array_append_val(ctx->base_facts, row);
}

static void add_points(OspreyContext *ctx, OspreyChunk pointer_chunk,
                       OspreyAddress target)
{
    OspreyPointsToFact row;
    memset(&row, 0, sizeof(row));
    row.pointer_chunk = pointer_chunk;
    row.target = target;
    row.sample_support = 1;
    g_array_append_val(ctx->points_facts, row);
}

static void add_alloc(OspreyContext *ctx, uint64_t site, uint64_t size)
{
    OspreyMallocFact row;
    memset(&row, 0, sizeof(row));
    row.site_pc = site;
    row.requested_size = size;
    row.sample_support = 1;
    g_array_append_val(ctx->alloc_facts, row);
}

static OspreyContext *new_relation_context(void)
{
    OspreyConfig config = relation_config();
    return osprey_new(&config);
}

static char *relation_dump_string(const OspreyRelations *relations)
{
    char *buffer = NULL;
    size_t length = 0;
    FILE *stream = open_memstream(&buffer, &length);
    CHECK(stream != NULL, "open relation dump stream");
    if (stream == NULL) return g_strdup("");
    osprey_relations_dump(relations, stream);
    fclose(stream);
    return buffer;
}

static const OspreyHintRelation *find_hint(const GArray *hints,
                                           OspreyAddress a1,
                                           OspreyAddress a2, int64_t size)
{
    for (guint i = 0; i < hints->len; i++) {
        const OspreyHintRelation *row = &g_array_index(
            hints, OspreyHintRelation, i);
        if (row->size == size &&
            osprey_relation_same_region(&row->a1.region, &a1.region) &&
            osprey_relation_same_region(&row->a2.region, &a2.region) &&
            row->a1.offset == a1.offset && row->a2.offset == a2.offset) {
            return row;
        }
    }
    return NULL;
}

static void populate_fixture(OspreyContext *ctx, bool reverse)
{
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyRegionId heap500 = make_region(OSPREY_REGION_HEAP_SITE, 0x500);
    OspreyRegionId heap600 = make_region(OSPREY_REGION_HEAP_SITE, 0x600);
    OspreyRegionId heap700 = make_region(OSPREY_REGION_HEAP_SITE, 0x700);
    OspreyRegionId heap800 = make_region(OSPREY_REGION_HEAP_SITE, 0x800);

    OspreyLogicalAccess accesses[11];
    memset(accesses, 0, sizeof(accesses));
#define ACCESS(_index, _pc, _region, _offset, _size, _count) do {          \
    accesses[_index].pc = (_pc);                                           \
    accesses[_index].chunk = make_chunk((_region), (_offset), (_size));    \
    accesses[_index].dynamic_count = (_count);                             \
    accesses[_index].sample_support = 1;                                   \
} while (0)
    ACCESS(0, 0x10, global, 0, 8, 3);
    ACCESS(1, 0x10, global, 8, 4, 3);
    ACCESS(2, 0x20, global, 0, 8, 5);
    ACCESS(3, 0x20, global, 8, 4, 2);
    ACCESS(4, 0x30, heap500, 0, 8, 1);
    ACCESS(5, 0x40, global, 0, 8, 1);
    ACCESS(6, 0x40, heap600, 0, 8, 1);
    ACCESS(7, 0x41, global, 16, 8, 1);
    ACCESS(8, 0x41, heap600, 16, 8, 1);
    ACCESS(9, 0x50, heap700, 8, 4, 1);
    ACCESS(10, 0x51, heap800, 8, 4, 1);
#undef ACCESS
    if (!reverse) {
        for (size_t i = 0; i < G_N_ELEMENTS(accesses); i++) {
            g_array_append_val(ctx->logical_access_facts, accesses[i]);
        }
    } else {
        for (size_t i = G_N_ELEMENTS(accesses); i != 0; i--) {
            g_array_append_val(ctx->logical_access_facts, accesses[i - 1]);
        }
    }

    if (!reverse) {
        add_copy(ctx, global, 0x100, 8, heap500, 0x100, 4);
        add_copy(ctx, global, 0x110, 4, heap500, 0x110, 16);
        add_copy(ctx, global, 0x120, 8, heap500, 0x139, 8);
    } else {
        add_copy(ctx, global, 0x120, 8, heap500, 0x139, 8);
        add_copy(ctx, global, 0x110, 4, heap500, 0x110, 16);
        add_copy(ctx, global, 0x100, 8, heap500, 0x100, 4);
    }

    OspreyAddress heap700_base = make_address(heap700, 0);
    OspreyAddress heap800_base = make_address(heap800, 0);
    if (!reverse) {
        add_base(ctx, heap700, 8, 4, heap700_base);
        add_base(ctx, heap800, 8, 4, heap800_base);
    } else {
        add_base(ctx, heap800, 8, 4, heap800_base);
        add_base(ctx, heap700, 8, 4, heap700_base);
    }
    OspreyChunk pointer = make_chunk(global, 0, 8);
    if (!reverse) {
        add_points(ctx, pointer, heap700_base);
        add_points(ctx, pointer, heap800_base);
    } else {
        add_points(ctx, pointer, heap800_base);
        add_points(ctx, pointer, heap700_base);
    }

    add_alloc(ctx, 0x500, 48);
    add_alloc(ctx, 0x500, 0);
    add_alloc(ctx, 0x500, 16);
    add_alloc(ctx, 0x600, 0);
}

static void test_helpers(void)
{
    registered++;
    executed++;
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyRegionId other = make_region(OSPREY_REGION_GLOBAL, 1);
    OspreyChunk first = make_chunk(region, 0, 8);
    OspreyChunk adjacent = make_chunk(region, 8, 4);
    OspreyChunk overlap = make_chunk(region, 4, 2);
    OspreyChunk disjoint = make_chunk(region, 8, 4);
    OspreyChunk different = make_chunk(other, 8, 4);
    CHECK(osprey_relation_same_region(&region, &region), "H01 equality");
    CHECK(!osprey_relation_same_region(&region, &other), "H01 mismatch");
    int64_t delta = 0;
    CHECK(osprey_relation_offset(&adjacent.address, &first.address, &delta) &&
          delta == 8, "H02 checked offset");
    CHECK(!osprey_relation_offset(&different.address, &first.address, &delta),
          "H02 different region has no result");
    OspreyAddress min_address = make_address(region, INT64_MIN);
    OspreyAddress max_address = make_address(region, INT64_MAX);
    CHECK(!osprey_relation_offset(&max_address, &min_address, &delta),
          "H02 overflow has no result");
    CHECK(osprey_relation_adjacent_chunk(&first, &adjacent), "H03 adjacent");
    CHECK(!osprey_relation_adjacent_chunk(&first, &different),
          "H03 different region");
    CHECK(osprey_relation_overlapping_chunk(&first, &overlap),
          "H04 directional overlap");
    CHECK(!osprey_relation_overlapping_chunk(&first, &disjoint),
          "H04 adjacent is not overlap");
    CHECK(!osprey_relation_overlapping_chunk(&first, &different),
          "H04 different region");
    OspreyChunk extreme = make_chunk(region, INT64_MAX, 8);
    CHECK(!osprey_relation_adjacent_chunk(&extreme, &adjacent),
          "H03 overflow rejected");

    OspreyAddress addresses[5];
    addresses[0] = make_address(region, -8);
    addresses[1] = make_address(region, 8);
    addresses[2] = make_address(region, 24);
    addresses[3] = addresses[2];
    addresses[4] = make_address(other, 40);
    CHECK(osprey_relation_addr_difference_gcd(addresses,
                                              G_N_ELEMENTS(addresses),
                                              &region, &delta) && delta == 16,
          "H05a sorted distinct address gcd");
    uint64_t sizes[] = { 48, 0, 16, 48 };
    uint64_t size_gcd = 0;
    CHECK(osprey_relation_size_difference_gcd(sizes, G_N_ELEMENTS(sizes),
                                               &size_gcd) && size_gcd == 16,
          "H05b sorted distinct size gcd");
    uint64_t singleton[] = { 0, 0 };
    CHECK(!osprey_relation_size_difference_gcd(singleton,
                                               G_N_ELEMENTS(singleton),
                                               &size_gcd),
          "H05b duplicate-only has no result");
}

static void test_logical_access_projection(void)
{
    registered++;
    executed++;
    OspreyContext *ctx = new_relation_context();
    size_t run_size = osprey_shared_run_size(&ctx->config);
    OspreySharedRun *run = g_malloc0(run_size);
    osprey_shared_run_reset(run, 1, &ctx->config);
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyAccessFact fact;
    memset(&fact, 0, sizeof(fact));
    fact.pc = 0x700;
    fact.chunk = make_chunk(global, 0x40, 8);
    fact.dynamic_count = 1;
    fact.sample_support = 1;
    fact.is_store = 0;
    fact.op_class = 1;
    CHECK(osprey_table_insert_access(run, &fact) == 1,
          "logical load insert");
    fact.dynamic_count = 2;
    fact.is_store = 1;
    CHECK(osprey_table_insert_access(run, &fact) == 1,
          "logical store insert");
    fact.dynamic_count = 3;
    fact.is_store = 0;
    fact.op_class = 2;
    CHECK(osprey_table_insert_access(run, &fact) == 1,
          "logical second-class insert");
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK,
          "logical first sample merge");
    CHECK(ctx->access_facts->len == 3, "F01 dimensions remain distinct");
    CHECK(ctx->logical_access_facts->len == 1,
          "projection has one logical access");
    if (ctx->logical_access_facts->len == 1) {
        OspreyLogicalAccess *row = &g_array_index(
            ctx->logical_access_facts, OspreyLogicalAccess, 0);
        CHECK(row->dynamic_count == 6,
              "projection saturating sum across dimensions");
        CHECK(row->sample_support == 1,
              "projection support is one per sample");
    }

    OspreySharedRun *second = g_malloc0(run_size);
    osprey_shared_run_reset(second, 2, &ctx->config);
    fact.dynamic_count = 4;
    fact.is_store = 0;
    fact.op_class = 1;
    CHECK(osprey_table_insert_access(second, &fact) == 1,
          "logical second sample insert");
    fact.dynamic_count = 5;
    fact.is_store = 1;
    CHECK(osprey_table_insert_access(second, &fact) == 1,
          "logical second sample store");
    CHECK(osprey_parent_merge_sample(ctx, second) == OSPREY_OK,
          "logical second sample merge");
    CHECK(ctx->logical_access_facts->len == 1,
          "logical key remains unique across samples");
    if (ctx->logical_access_facts->len == 1) {
        OspreyLogicalAccess *row = &g_array_index(
            ctx->logical_access_facts, OspreyLogicalAccess, 0);
        CHECK(row->dynamic_count == 15,
              "logical dynamic total spans samples");
        CHECK(row->sample_support == 2,
              "logical support spans samples once");
    }

    OspreySharedRun *saturated = g_malloc0(run_size);
    osprey_shared_run_reset(saturated, 3, &ctx->config);
    fact.dynamic_count = UINT32_MAX;
    fact.is_store = 0;
    fact.op_class = 1;
    CHECK(osprey_table_insert_access(saturated, &fact) == 1,
          "logical saturation load insert");
    fact.dynamic_count = 1;
    fact.is_store = 1;
    fact.op_class = 2;
    CHECK(osprey_table_insert_access(saturated, &fact) == 1,
          "logical saturation store insert");
    CHECK(osprey_parent_merge_sample(ctx, saturated) == OSPREY_OK,
          "logical saturation sample merge");
    CHECK(ctx->logical_access_facts->len == 1,
          "logical saturation key remains unique");
    if (ctx->logical_access_facts->len == 1) {
        OspreyLogicalAccess *row = &g_array_index(
            ctx->logical_access_facts, OspreyLogicalAccess, 0);
        CHECK(row->dynamic_count == UINT32_MAX,
              "logical dynamic total saturates");
        CHECK(row->sample_support == 3,
              "logical saturation support remains per sample");
    }
    osprey_free(ctx);
    g_free(saturated);
    g_free(second);
    g_free(run);
}

static void test_logical_access_prefix_union(void)
{
    registered++;
    executed++;
    OspreyContext *ctx = new_relation_context();
    size_t run_size = osprey_shared_run_size(&ctx->config);
    OspreySharedRun *run = g_malloc0(run_size);
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyAccessFact fact;

    osprey_shared_run_reset(run, 4, &ctx->config);
    memset(&fact, 0, sizeof(fact));
    fact.pc = 0x710;
    fact.chunk = make_chunk(global, 0x48, 8);
    fact.dynamic_count = 2;
    fact.sample_support = 1;
    fact.op_class = 1;
    CHECK(osprey_table_insert_access(run, &fact) == 1,
          "logical prefix insert");
    CHECK(osprey_shared_run_freeze_prefix(ctx, run),
          "logical prefix freeze");
    osprey_shared_run_prepare(ctx, run, 4);

    fact.dynamic_count = 3;
    CHECK(osprey_table_insert_access(run, &fact) == 1,
          "logical repeated suffix insert");
    fact.dynamic_count = 5;
    fact.is_store = 1;
    CHECK(osprey_table_insert_access(run, &fact) == 1,
          "logical distinct suffix insert");
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK,
          "logical prefix-union sample merge");
    CHECK(ctx->access_facts->len == 2,
          "prefix-union preserves full F01 identities");
    CHECK(ctx->logical_access_facts->len == 1,
          "prefix-union projects one logical access");
    if (ctx->logical_access_facts->len == 1) {
        const OspreyLogicalAccess *row = &g_array_index(
            ctx->logical_access_facts, OspreyLogicalAccess, 0);
        CHECK(row->dynamic_count == 10,
              "prefix-union sums all dynamic observations");
        CHECK(row->sample_support == 1,
              "prefix-union contributes one sample support");
    }

    osprey_free(ctx);
    g_free(run);
}

static void test_relation_arithmetic_rejection(void)
{
    registered++;
    executed++;
    OspreyContext *ctx = new_relation_context();
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyRegionId heap = make_region(OSPREY_REGION_HEAP_SITE, 0x900);
    add_copy(ctx, global, INT64_MIN, 8, heap, INT64_MIN, 8);
    add_copy(ctx, global, INT64_MAX, 8, heap, INT64_MAX, 8);
    CHECK(osprey_relations_build(ctx) == OSPREY_RELATION_ARITHMETIC,
          "R10 signed subtraction overflow rejects construction");
    CHECK(ctx->relations == NULL,
          "relation arithmetic failure installs no partial result");
    osprey_free(ctx);
}

static void check_relation_case(const char *label, OspreyContext *ctx,
                                const int expected[12])
{
    const GArray *arrays[12];
    OspreyRelations *reference = NULL;
    char *optimized_dump;
    char *reference_dump;
    registered++;
    executed++;
    if (osprey_relations_build(ctx) != OSPREY_OK || ctx->relations == NULL) {
        fprintf(stderr, "FAIL: %s optimized relation construction\n", label);
        failures++;
        osprey_free(ctx);
        return;
    }
    if (!stage3_reference_build(ctx, &reference) || reference == NULL) {
        fprintf(stderr, "FAIL: %s reference relation construction\n", label);
        failures++;
        osprey_free(ctx);
        return;
    }
    optimized_dump = relation_dump_string(ctx->relations);
    reference_dump = relation_dump_string(reference);
    if (strcmp(optimized_dump, reference_dump) != 0) {
        fprintf(stderr, "FAIL: %s optimized/reference mismatch\n", label);
        failures++;
    }
    arrays[0] = ctx->relations->r01_accessed;
    arrays[1] = ctx->relations->r02_accessed;
    arrays[2] = ctx->relations->r03_single_chunk;
    arrays[3] = ctx->relations->r04_multi_chunk;
    arrays[4] = ctx->relations->r05_high_address;
    arrays[5] = ctx->relations->r06_low_address;
    arrays[6] = ctx->relations->r07_most_frequent;
    arrays[7] = ctx->relations->r08_constant_alloc;
    arrays[8] = ctx->relations->r09_alloc_unit;
    arrays[9] = ctx->relations->r10_data_flow;
    arrays[10] = ctx->relations->r11_unified_access;
    arrays[11] = ctx->relations->r12_points_to;
    for (unsigned i = 0; i < G_N_ELEMENTS(arrays); i++) {
        if (expected[i] >= 0 && arrays[i]->len != (guint)expected[i]) {
            fprintf(stderr, "FAIL: %s R%02u expected %d rows, got %u\n",
                    label, i + 1, expected[i], arrays[i]->len);
            failures++;
        }
    }
    g_free(optimized_dump);
    g_free(reference_dump);
    osprey_relations_free(reference);
    osprey_free(ctx);
}

static void add_logical(OspreyContext *ctx, uint64_t pc,
                        OspreyRegionId region, int64_t offset,
                        uint64_t size, uint32_t dynamic_count)
{
    OspreyLogicalAccess row;
    memset(&row, 0, sizeof(row));
    row.pc = pc;
    row.chunk = make_chunk(region, offset, size);
    row.dynamic_count = dynamic_count;
    row.sample_support = 1;
    g_array_append_val(ctx->logical_access_facts, row);
}

static void expected_only(int expected[12], unsigned relation, int count)
{
    for (unsigned i = 0; i < 12; i++) expected[i] = -1;
    expected[relation - 1] = count;
}

static void test_relation_condition_matrix(void)
{
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyRegionId heap1 = make_region(OSPREY_REGION_HEAP_SITE, 0x100);
    OspreyRegionId heap2 = make_region(OSPREY_REGION_HEAP_SITE, 0x200);
    int expected[12];
    OspreyContext *ctx;

    ctx = new_relation_context();
    add_logical(ctx, 1, global, 0, 8, 1);
    expected_only(expected, 1, 1);
    check_relation_case("R01 positive", ctx, expected);
    ctx = new_relation_context();
    expected_only(expected, 1, 0);
    check_relation_case("R01 condition off", ctx, expected);

    ctx = new_relation_context();
    add_logical(ctx, 2, global, 0, 8, 1);
    expected_only(expected, 2, 1);
    check_relation_case("R02 positive", ctx, expected);
    ctx = new_relation_context();
    expected_only(expected, 2, 0);
    check_relation_case("R02 condition off", ctx, expected);

    ctx = new_relation_context();
    add_logical(ctx, 3, global, 0, 8, 1);
    expected_only(expected, 3, 1);
    check_relation_case("R03 positive", ctx, expected);
    ctx = new_relation_context();
    add_logical(ctx, 3, global, 0, 8, 1);
    add_logical(ctx, 3, global, 8, 8, 1);
    expected_only(expected, 3, 0);
    expected[3] = 1;
    check_relation_case("R03 condition off", ctx, expected);

    ctx = new_relation_context();
    add_logical(ctx, 4, global, 0, 8, 1);
    add_logical(ctx, 4, global, 8, 8, 1);
    expected_only(expected, 4, 1);
    check_relation_case("R04 positive", ctx, expected);
    ctx = new_relation_context();
    add_logical(ctx, 4, global, 0, 8, 1);
    expected_only(expected, 4, 0);
    check_relation_case("R04 condition off", ctx, expected);

    ctx = new_relation_context();
    add_logical(ctx, 5, heap1, 4, 8, 1);
    expected_only(expected, 5, 1);
    check_relation_case("R05 positive", ctx, expected);
    ctx = new_relation_context();
    expected_only(expected, 5, 0);
    check_relation_case("R05 condition off", ctx, expected);

    ctx = new_relation_context();
    add_logical(ctx, 6, heap1, 4, 8, 1);
    expected_only(expected, 6, 1);
    check_relation_case("R06 positive", ctx, expected);
    ctx = new_relation_context();
    expected_only(expected, 6, 0);
    check_relation_case("R06 condition off", ctx, expected);

    ctx = new_relation_context();
    add_logical(ctx, 7, global, 0, 4, 9);
    add_logical(ctx, 7, global, 0, 8, 3);
    add_logical(ctx, 7, global, 8, 4, 9);
    expected_only(expected, 7, 2);
    check_relation_case("R07 tied addresses and widths", ctx, expected);
    ctx = new_relation_context();
    add_logical(ctx, 7, global, 0, 4, 9);
    add_logical(ctx, 7, global, 8, 4, 3);
    expected_only(expected, 7, 1);
    check_relation_case("R07 condition off", ctx, expected);

    ctx = new_relation_context();
    add_alloc(ctx, 8, 0);
    expected_only(expected, 8, 1);
    check_relation_case("R08 zero-size positive", ctx, expected);
    ctx = new_relation_context();
    add_alloc(ctx, 8, 0);
    add_alloc(ctx, 8, 16);
    expected_only(expected, 8, 0);
    expected[8] = 1;
    check_relation_case("R08 condition off", ctx, expected);

    ctx = new_relation_context();
    add_alloc(ctx, 9, 0);
    add_alloc(ctx, 9, 16);
    add_alloc(ctx, 9, 48);
    expected_only(expected, 9, 1);
    check_relation_case("R09 gcd positive", ctx, expected);
    ctx = new_relation_context();
    add_alloc(ctx, 9, 16);
    add_alloc(ctx, 9, 16);
    expected_only(expected, 9, 0);
    check_relation_case("R09 condition off", ctx, expected);

    ctx = new_relation_context();
    add_copy(ctx, global, 0x100, 4, heap1, 0x100, 8);
    add_copy(ctx, global, 0x110, 16, heap1, 0x110, 4);
    expected_only(expected, 10, 1);
    check_relation_case("R10 unequal widths positive", ctx, expected);
    ctx = new_relation_context();
    add_copy(ctx, global, 0x100, 4, heap1, 0x100, 8);
    add_copy(ctx, global, 0x110, 16, heap1, 0x111, 4);
    expected_only(expected, 10, 0);
    check_relation_case("R10 wrong destination delta", ctx, expected);
    ctx = new_relation_context();
    add_copy(ctx, global, 0x100, 4, heap1, 0x100, 8);
    add_copy(ctx, global, 0x111, 4, heap1, 0x110, 8);
    expected_only(expected, 10, 0);
    check_relation_case("R10 wrong source delta", ctx, expected);
    ctx = new_relation_context();
    add_copy(ctx, global, 0x100, 4, heap1, 0x100, 8);
    add_copy(ctx, heap2, 0x110, 4, heap1, 0x110, 8);
    expected_only(expected, 10, 0);
    check_relation_case("R10 source region mismatch", ctx, expected);
    ctx = new_relation_context();
    add_copy(ctx, global, 0x100, 4, heap1, 0x100, 8);
    add_copy(ctx, global, 0x110, 4, heap2, 0x110, 8);
    expected_only(expected, 10, 0);
    check_relation_case("R10 destination region mismatch", ctx, expected);

    ctx = new_relation_context();
    add_logical(ctx, 11, global, 0, 4, 1);
    add_logical(ctx, 11, heap1, 0, 4, 1);
    add_logical(ctx, 12, global, 16, 4, 1);
    add_logical(ctx, 12, heap1, 16, 4, 1);
    expected_only(expected, 11, 1);
    check_relation_case("R11 two instructions positive", ctx, expected);
    ctx = new_relation_context();
    add_logical(ctx, 11, global, 0, 4, 1);
    add_logical(ctx, 11, heap1, 0, 4, 1);
    add_logical(ctx, 12, global, 16, 4, 1);
    add_logical(ctx, 12, heap1, 17, 4, 1);
    expected_only(expected, 11, 0);
    check_relation_case("R11 wrong corresponding offset", ctx, expected);
    ctx = new_relation_context();
    add_logical(ctx, 11, global, 0, 4, 1);
    add_logical(ctx, 11, heap1, 0, 4, 1);
    add_logical(ctx, 11, global, 16, 4, 1);
    add_logical(ctx, 11, heap1, 16, 4, 1);
    expected_only(expected, 11, 0);
    check_relation_case("R11 same instruction near miss", ctx, expected);

    OspreyChunk pointer = make_chunk(global, 0, 8);
    OspreyAddress target1 = make_address(heap1, 0);
    OspreyAddress target2 = make_address(heap2, 0);
    ctx = new_relation_context();
    add_points(ctx, pointer, target1);
    add_points(ctx, pointer, target2);
    add_logical(ctx, 13, heap1, 8, 4, 1);
    add_logical(ctx, 13, heap2, 8, 4, 1);
    add_base(ctx, heap1, 8, 4, target1);
    add_base(ctx, heap2, 8, 4, target2);
    expected_only(expected, 12, 1);
    check_relation_case("R12 pointer cell positive", ctx, expected);
    ctx = new_relation_context();
    add_points(ctx, pointer, target1);
    add_points(ctx, pointer, target2);
    add_logical(ctx, 13, heap1, 8, 4, 1);
    add_logical(ctx, 13, heap2, 8, 4, 1);
    add_base(ctx, heap1, 8, 4, target1);
    expected_only(expected, 12, 0);
    check_relation_case("R12 missing BaseAddr", ctx, expected);

    ctx = new_relation_context();
    add_points(ctx, pointer, target1);
    OspreyChunk second_pointer = make_chunk(global, 16, 8);
    add_points(ctx, second_pointer, target2);
    add_logical(ctx, 13, heap1, 8, 4, 1);
    add_logical(ctx, 13, heap2, 8, 4, 1);
    add_base(ctx, heap1, 8, 4, target1);
    add_base(ctx, heap2, 8, 4, target2);
    expected_only(expected, 12, 0);
    check_relation_case("R12 different pointer cell", ctx, expected);

    ctx = new_relation_context();
    add_points(ctx, pointer, target1);
    add_points(ctx, pointer, target2);
    add_logical(ctx, 13, heap1, 8, 4, 1);
    add_logical(ctx, 13, heap2, 9, 4, 1);
    add_base(ctx, heap1, 8, 4, target1);
    add_base(ctx, heap2, 9, 4, target2);
    expected_only(expected, 12, 0);
    check_relation_case("R12 wrong field offset", ctx, expected);

    ctx = new_relation_context();
    add_points(ctx, pointer, target1);
    add_points(ctx, pointer, target2);
    add_logical(ctx, 13, heap1, 8, 4, 1);
    add_base(ctx, heap1, 8, 4, target1);
    add_base(ctx, heap2, 8, 4, target2);
    expected_only(expected, 12, 0);
    check_relation_case("R12 unaccessed target chunk", ctx, expected);
}

static void test_r10_duplicate_fact_dedup(void)
{
    registered++;
    executed++;
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyRegionId heap = make_region(OSPREY_REGION_HEAP_SITE, 0x100);
    OspreyContext *ctx = new_relation_context();

    add_copy(ctx, global, 0x100, 4, heap, 0x100, 8);
    add_copy(ctx, global, 0x100, 4, heap, 0x100, 8);
    add_copy(ctx, global, 0x110, 16, heap, 0x110, 4);
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "R10 duplicate-fact relation construction");
    CHECK(ctx->relations != NULL && ctx->relations->r10_data_flow->len == 1,
          "R10 duplicate facts retain one hint");
    if (ctx->relations != NULL && ctx->relations->r10_data_flow->len == 1) {
        const OspreyHintRelation *hint = &g_array_index(
            ctx->relations->r10_data_flow, OspreyHintRelation, 0);
        CHECK(hint->witness_count == 1,
              "R10 duplicate facts count one semantic witness");
    }
    osprey_free(ctx);
}

static void test_fixture_and_reference(void)
{
    registered++;
    executed++;
    OspreyContext *optimized_context = new_relation_context();
    OspreyContext *permuted_context = new_relation_context();
    populate_fixture(optimized_context, false);
    populate_fixture(permuted_context, true);
    CHECK(osprey_relations_build(optimized_context) == OSPREY_OK,
          "optimized fixture relations");
    CHECK(osprey_relations_build(permuted_context) == OSPREY_OK,
          "permuted fixture relations");
    OspreyRelations *reference = NULL;
    CHECK(stage3_reference_build(optimized_context, &reference),
          "reference fixture relations");
    if (optimized_context->relations != NULL && reference != NULL) {
        char *optimized_dump = relation_dump_string(optimized_context->relations);
        char *reference_dump = relation_dump_string(reference);
        char *permuted_dump = relation_dump_string(permuted_context->relations);
        CHECK(strcmp(optimized_dump, reference_dump) == 0,
              "optimized fixture equals slow reference");
        CHECK(strcmp(optimized_dump, permuted_dump) == 0,
              "fixture permutation is deterministic");
        CHECK(osprey_relations_build(optimized_context) == OSPREY_OK,
              "repeated fixture relations");
        char *repeated_dump = relation_dump_string(optimized_context->relations);
        CHECK(strcmp(optimized_dump, repeated_dump) == 0,
              "repeated relation build is deterministic");
        g_free(optimized_dump);
        g_free(reference_dump);
        g_free(permuted_dump);
        g_free(repeated_dump);

        OspreyRelations *r = optimized_context->relations;
        CHECK(r->r01_accessed->len == 11, "R01 exact row count");
        CHECK(r->r02_accessed->len == 8, "R02 distinct chunk count");
        CHECK(r->r03_single_chunk->len == 7, "R03 singleton groups");
        CHECK(r->r04_multi_chunk->len == 2, "R04 multi groups");
        CHECK(r->r05_high_address->len == 9 && r->r06_low_address->len == 9,
              "R05/R06 extrema per group");
        CHECK(r->r08_constant_alloc->len == 1 &&
              r->r09_alloc_unit->len == 1,
              "R08/R09 mutually exclusive site outputs");
        CHECK(g_array_index(r->r08_constant_alloc, OspreyAllocRelation, 0)
                  .size == 0,
              "R08 preserves zero-size singleton");
        CHECK(g_array_index(r->r09_alloc_unit, OspreyAllocRelation, 0).size ==
                  16,
              "R09 uses size-difference gcd");
        OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
        OspreyAddress g0 = make_address(global, 0);
        OspreyAddress g8 = make_address(global, 8);
        const OspreyHintRelation *r10 = find_hint(
            r->r10_data_flow, make_address(global, 0x100),
            make_address(make_region(OSPREY_REGION_HEAP_SITE, 0x500), 0x100),
            16);
        CHECK(r10 != NULL && r10->witness_count == 1,
              "R10 uses equal address delta with unequal widths");
        const OspreyHintRelation *r11 = find_hint(
            r->r11_unified_access, g0,
            make_address(make_region(OSPREY_REGION_HEAP_SITE, 0x600), 0), 16);
        CHECK(r11 != NULL && r11->witness_count == 1,
              "R11 joins distinct instructions and region roles");
        const OspreyHintRelation *r12 = find_hint(
            r->r12_points_to,
            make_address(make_region(OSPREY_REGION_HEAP_SITE, 0x700), 0),
            make_address(make_region(OSPREY_REGION_HEAP_SITE, 0x800), 0), 8);
        CHECK(r12 != NULL && r12->witness_count == 1,
              "R12 joins one pointer cell with two targets");
        CHECK(g8.offset == 8, "fixture address helper remains explicit");
    }
    osprey_relations_free(reference);
    osprey_free(permuted_context);
    osprey_free(optimized_context);
}

/* Fixed-seed small bounded inputs exercise all sort/dedup paths without
 * relying on a hash-table iteration order. */
typedef struct RandomFixture {
    GArray *access;
    GArray *copies;
    GArray *bases;
    GArray *points;
    GArray *allocs;
} RandomFixture;

static uint32_t next_random(uint32_t *state)
{
    uint32_t value = *state;
    value ^= value << 13;
    value ^= value >> 17;
    value ^= value << 5;
    *state = value;
    return value;
}

static OspreyRegionId random_region(uint32_t *state)
{
    unsigned kind = next_random(state) % 3;
    uint64_t site = kind == OSPREY_REGION_GLOBAL
        ? 0 : (uint64_t)(next_random(state) % 4 + 1) * 0x100;
    return make_region((OspreyRegionKind)kind, site);
}

static int64_t random_offset(uint32_t *state)
{
    return (int64_t)(next_random(state) % 17) - 8;
}

static uint64_t random_width(uint32_t *state)
{
    static const uint64_t widths[] = { 1, 2, 4, 8, 16 };
    return widths[next_random(state) % G_N_ELEMENTS(widths)];
}

static RandomFixture random_fixture(uint32_t *state)
{
    RandomFixture fixture;
    fixture.access = g_array_new(FALSE, FALSE, sizeof(OspreyLogicalAccess));
    fixture.copies = g_array_new(FALSE, FALSE, sizeof(OspreyCopyFact));
    fixture.bases = g_array_new(FALSE, FALSE, sizeof(OspreyBaseFact));
    fixture.points = g_array_new(FALSE, FALSE, sizeof(OspreyPointsToFact));
    fixture.allocs = g_array_new(FALSE, FALSE, sizeof(OspreyMallocFact));
    /* Six source rows plus duplicates at indices 0 and 4 keep every
     * materialized family at or below the required eight-row bound. */
    unsigned access_count = next_random(state) % 6 + 1;
    unsigned copy_count = next_random(state) % 6 + 1;
    unsigned base_count = next_random(state) % 6 + 1;
    unsigned point_count = next_random(state) % 6 + 1;
    unsigned alloc_count = next_random(state) % 6 + 1;
    for (unsigned i = 0; i < access_count; i++) {
        OspreyLogicalAccess row;
        memset(&row, 0, sizeof(row));
        row.pc = next_random(state) % 4 + 1;
        row.chunk = make_chunk(random_region(state), random_offset(state),
                               random_width(state));
        row.dynamic_count = i == 0 ? UINT32_MAX : next_random(state) % 32;
        row.sample_support = 1;
        g_array_append_val(fixture.access, row);
        if ((i & 3u) == 0) g_array_append_val(fixture.access, row);
    }
    for (unsigned i = 0; i < copy_count; i++) {
        OspreyCopyFact row;
        memset(&row, 0, sizeof(row));
        row.source = make_chunk(random_region(state), random_offset(state),
                                random_width(state));
        row.destination = make_chunk(random_region(state), random_offset(state),
                                     random_width(state));
        row.sample_support = 1;
        g_array_append_val(fixture.copies, row);
        if ((i & 3u) == 0) g_array_append_val(fixture.copies, row);
    }
    for (unsigned i = 0; i < base_count; i++) {
        OspreyBaseFact row;
        memset(&row, 0, sizeof(row));
        row.chunk = make_chunk(random_region(state), random_offset(state),
                               random_width(state));
        row.base = make_address(random_region(state), random_offset(state));
        row.sample_support = 1;
        g_array_append_val(fixture.bases, row);
        if ((i & 3u) == 0) g_array_append_val(fixture.bases, row);
    }
    for (unsigned i = 0; i < point_count; i++) {
        OspreyPointsToFact row;
        memset(&row, 0, sizeof(row));
        row.pointer_chunk = make_chunk(random_region(state), random_offset(state),
                                       random_width(state));
        row.target = make_address(random_region(state), random_offset(state));
        row.sample_support = 1;
        g_array_append_val(fixture.points, row);
        if ((i & 3u) == 0) g_array_append_val(fixture.points, row);
    }
    for (unsigned i = 0; i < alloc_count; i++) {
        OspreyMallocFact row;
        memset(&row, 0, sizeof(row));
        row.site_pc = (next_random(state) % 3 + 1) * 0x100;
        row.requested_size = (next_random(state) % 4) * 16;
        row.sample_support = 1;
        g_array_append_val(fixture.allocs, row);
        if ((i & 3u) == 0) g_array_append_val(fixture.allocs, row);
    }
    return fixture;
}

static void free_random_fixture(RandomFixture *fixture)
{
    g_array_free(fixture->access, TRUE);
    g_array_free(fixture->copies, TRUE);
    g_array_free(fixture->bases, TRUE);
    g_array_free(fixture->points, TRUE);
    g_array_free(fixture->allocs, TRUE);
}

static void append_random_order(GArray *destination, const GArray *source,
                                uint32_t *state, size_t element_size)
{
    guint *order = g_new(guint, source->len);
    for (guint i = 0; i < source->len; i++) order[i] = i;
    for (guint i = source->len; i > 1; i--) {
        guint j = next_random(state) % i;
        guint swap = order[i - 1];
        order[i - 1] = order[j];
        order[j] = swap;
    }
    for (guint i = 0; i < source->len; i++) {
        gpointer row = (guint8 *)source->data +
                       (size_t)order[i] * element_size;
        g_array_append_vals(destination, row, 1);
    }
    g_free(order);
}

static void install_random_fixture(OspreyContext *ctx,
                                   const RandomFixture *fixture,
                                   uint32_t *state)
{
    append_random_order(ctx->logical_access_facts, fixture->access, state,
                        sizeof(OspreyLogicalAccess));
    append_random_order(ctx->copy_facts, fixture->copies, state,
                        sizeof(OspreyCopyFact));
    append_random_order(ctx->base_facts, fixture->bases, state,
                        sizeof(OspreyBaseFact));
    append_random_order(ctx->points_facts, fixture->points, state,
                        sizeof(OspreyPointsToFact));
    append_random_order(ctx->alloc_facts, fixture->allocs, state,
                        sizeof(OspreyMallocFact));
}

static void dump_random_chunk(const char *label, const OspreyChunk *chunk)
{
    fprintf(stderr, "%s=%u:%" PRIu64 ":%" PRIu64 ":%" PRId64
            ":%" PRIu64, label, (unsigned)chunk->address.region.kind,
            chunk->address.region.code_image_id,
            chunk->address.region.site_offset, chunk->address.offset,
            chunk->size);
}

static void dump_random_fixture(const RandomFixture *fixture)
{
    for (guint i = 0; i < fixture->access->len; i++) {
        const OspreyLogicalAccess *row = &g_array_index(
            fixture->access, OspreyLogicalAccess, i);
        fprintf(stderr, "  access pc=%" PRIu64 " ", row->pc);
        dump_random_chunk("chunk", &row->chunk);
        fprintf(stderr, " dynamic=%" PRIu32 " support=%" PRIu32 "\n",
                row->dynamic_count, row->sample_support);
    }
    for (guint i = 0; i < fixture->copies->len; i++) {
        const OspreyCopyFact *row = &g_array_index(
            fixture->copies, OspreyCopyFact, i);
        fputs("  copy ", stderr);
        dump_random_chunk("source", &row->source);
        fputc(' ', stderr);
        dump_random_chunk("destination", &row->destination);
        fputc('\n', stderr);
    }
    for (guint i = 0; i < fixture->bases->len; i++) {
        const OspreyBaseFact *row = &g_array_index(
            fixture->bases, OspreyBaseFact, i);
        fputs("  base ", stderr);
        dump_random_chunk("chunk", &row->chunk);
        fprintf(stderr, " base=%u:%" PRIu64 ":%" PRIu64 ":%" PRId64
                "\n", (unsigned)row->base.region.kind,
                row->base.region.code_image_id, row->base.region.site_offset,
                row->base.offset);
    }
    for (guint i = 0; i < fixture->points->len; i++) {
        const OspreyPointsToFact *row = &g_array_index(
            fixture->points, OspreyPointsToFact, i);
        fputs("  points ", stderr);
        dump_random_chunk("chunk", &row->pointer_chunk);
        fprintf(stderr, " target=%u:%" PRIu64 ":%" PRIu64 ":%" PRId64
                "\n", (unsigned)row->target.region.kind,
                row->target.region.code_image_id,
                row->target.region.site_offset, row->target.offset);
    }
    for (guint i = 0; i < fixture->allocs->len; i++) {
        const OspreyMallocFact *row = &g_array_index(
            fixture->allocs, OspreyMallocFact, i);
        fprintf(stderr, "  alloc site=%" PRIu64 " size=%" PRIu64 "\n",
                row->site_pc, row->requested_size);
    }
}

static void test_generated_differential(void)
{
    registered++;
    executed++;
    const uint32_t initial_seed = 0x51a7e3d1u;
    uint32_t state = initial_seed;
    const unsigned cases = 2000;
    for (unsigned case_number = 0; case_number < cases; case_number++) {
        uint32_t case_seed = state;
        RandomFixture fixture = random_fixture(&state);
        OspreyContext *optimized = new_relation_context();
        OspreyContext *permuted = new_relation_context();
        install_random_fixture(optimized, &fixture, &state);
        install_random_fixture(permuted, &fixture, &state);
        OspreyStatus optimized_status = osprey_relations_build(optimized);
        OspreyStatus permuted_status = osprey_relations_build(permuted);
        if (optimized_status != OSPREY_OK || permuted_status != OSPREY_OK) {
            fprintf(stderr, "FAIL: generated case %u seed 0x%08" PRIx32
                    " input access=%u copies=%u bases=%u points=%u allocs=%u"
                    " relation status %d/%d\n", case_number, case_seed,
                    fixture.access->len, fixture.copies->len,
                    fixture.bases->len, fixture.points->len,
                    fixture.allocs->len, optimized_status, permuted_status);
            dump_random_fixture(&fixture);
            failures++;
        } else {
            OspreyRelations *reference = NULL;
            bool reference_ok = stage3_reference_build(optimized, &reference);
            if (!reference_ok || reference == NULL) {
                fprintf(stderr, "FAIL: generated case %u seed 0x%08" PRIx32
                        " input access=%u copies=%u bases=%u points=%u allocs=%u"
                        " reference construction\n", case_number, case_seed,
                        fixture.access->len, fixture.copies->len,
                        fixture.bases->len, fixture.points->len,
                        fixture.allocs->len);
                dump_random_fixture(&fixture);
                failures++;
            } else {
                char *optimized_dump = relation_dump_string(optimized->relations);
                char *reference_dump = relation_dump_string(reference);
                char *permuted_dump = relation_dump_string(permuted->relations);
                if (strcmp(optimized_dump, reference_dump) != 0 ||
                    strcmp(optimized_dump, permuted_dump) != 0) {
                    fprintf(stderr, "FAIL: generated case %u seed 0x%08" PRIx32
                            " input access=%u copies=%u bases=%u points=%u allocs=%u"
                            " optimized/reference/permutation mismatch\n",
                            case_number, case_seed, fixture.access->len,
                            fixture.copies->len, fixture.bases->len,
                            fixture.points->len, fixture.allocs->len);
                    dump_random_fixture(&fixture);
                    failures++;
                }
                g_free(optimized_dump);
                g_free(reference_dump);
                g_free(permuted_dump);
                osprey_relations_free(reference);
            }
        }
        osprey_free(permuted);
        osprey_free(optimized);
        free_random_fixture(&fixture);
    }
}

int main(void)
{
    test_helpers();
    test_logical_access_projection();
    test_logical_access_prefix_union();
    test_relation_arithmetic_rejection();
    test_relation_condition_matrix();
    test_r10_duplicate_fact_dedup();
    test_fixture_and_reference();
    test_generated_differential();
    printf("stage3_relations: %u/%u cases, generated 2000, failures %u\n",
           executed, registered, failures);
    return failures == 0 && executed == registered ? EXIT_SUCCESS : EXIT_FAILURE;
}
