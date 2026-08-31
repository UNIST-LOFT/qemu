#include "osprey.h"
#include "osprey-internal.h"

#include <float.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned failures;
static unsigned registered;
static unsigned executed;

#define CHECK(condition, message) do {                                      \
    if (!(condition)) {                                                      \
        fprintf(stderr, "FAIL: %s (line %d)\n", (message), __LINE__);     \
        failures++;                                                          \
    }                                                                            \
} while (0)

#define RUN(test) do {                                                       \
    registered++;                                                            \
    test();                                                                  \
    executed++;                                                              \
} while (0)

static OspreyConfig decode_config(void)
{
    OspreyConfig config;
    memset(&config, 0, sizeof(config));
    config.enabled = true;
    config.shared_bytes = 1u << 20;
    config.max_facts = 1024;
    config.max_chunks_per_region = 128;
    config.max_candidates_per_kind_region = 4096;
    config.max_variables = 1024;
    config.max_factors = 4096;
    config.max_exact_clique_vars = 20;
    config.max_exact_table_bytes = 1u << 20;
    config.max_bp_table_bytes = 1u << 20;
    config.report_threshold = 0.6;
    return config;
}

static OspreyRegionId make_region(OspreyRegionKind kind, uint64_t image,
                                  uint64_t site)
{
    OspreyRegionId region;
    memset(&region, 0, sizeof(region));
    region.kind = kind;
    region.code_image_id = image;
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

static OspreyContext *new_decode_context(void)
{
    OspreyConfig config = decode_config();
    OspreyContext *ctx = osprey_new(&config);
    if (ctx != NULL) {
        ctx->graph = osprey_graph_new();
        if (ctx->graph != NULL) ctx->graph->extents_built = true;
    }
    return ctx;
}

static void add_extent(OspreyContext *ctx, OspreyRegionId region,
                       int64_t lo, int64_t hi)
{
    OspreyRegionExtent extent;
    memset(&extent, 0, sizeof(extent));
    extent.region = region;
    extent.lo = lo;
    extent.hi = hi;
    g_array_append_val(ctx->graph->extents, extent);
}

static uint32_t add_payload(OspreyContext *ctx, uint8_t kind,
                            const OspreyVarPayload *payload)
{
    OspreyInternResult result = osprey_intern_var(ctx, kind, payload);
    CHECK(result.id != UINT32_MAX, "decoder fixture variable inserted");
    return result.id;
}

static uint32_t add_chunk_var(OspreyContext *ctx, uint8_t kind,
                              OspreyChunk chunk)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.chunk = chunk;
    return add_payload(ctx, kind, &payload);
}

static void set_belief(OspreyContext *ctx, uint32_t id, double belief)
{
    OspreyVar *variable = &g_array_index(ctx->graph->vars, OspreyVar, id);
    variable->belief = belief;
    variable->belief_valid = 1;
}

static void set_all_beliefs(OspreyContext *ctx, double belief)
{
    for (guint i = 0; i < ctx->graph->vars->len; i++) {
        set_belief(ctx, i, belief);
    }
}

static char *dump_input(const OspreyDecodeInput *input)
{
    char *data = NULL;
    size_t length = 0;
    FILE *out = open_memstream(&data, &length);
    if (out == NULL) return NULL;
    if (!osprey_decode_input_dump_file(input, out) || fclose(out) != 0) {
        free(data);
        return NULL;
    }
    return data;
}

static bool build_input(OspreyContext *ctx, OspreyDecodeInput **out)
{
    OspreyStatus status = osprey_decode_input_build(ctx, out);
    CHECK(status == OSPREY_OK, "valid decoder input builds");
    return status == OSPREY_OK;
}

static OspreyContext *make_projection_context(unsigned order)
{
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0x101, 0x500);
    OspreyRegionId heap = make_region(OSPREY_REGION_HEAP_SITE, 0x202, 0x120);
    OspreyRegionId stack = make_region(OSPREY_REGION_STACK_FUNCTION,
                                       0x303, 0x80);
    OspreyChunk primitive = make_chunk(global, 32, 8);
    OspreyChunk scalar = make_chunk(global, 0, 4);
    OspreyChunk field_a = make_chunk(heap, 8, 8);
    OspreyChunk field_b = make_chunk(heap, 24, 4);
    OspreyChunk pointer = make_chunk(global, 96, sizeof(target_ulong));
    OspreyVarPayload payloads[12];
    uint8_t kinds[12];
    size_t count = 0;

    memset(payloads, 0, sizeof(payloads));
    kinds[count] = OSPREY_PRED_PRIMITIVE_VAR;
    payloads[count++].chunk = primitive;
    kinds[count] = OSPREY_PRED_SCALAR;
    payloads[count++].chunk = scalar;
    kinds[count] = OSPREY_PRED_ARRAY;
    payloads[count].segment.a1 = make_address(global, 0);
    payloads[count].segment.a2 = make_address(global, 18);
    payloads[count++].segment.size = 8; /* retained: graph-valid, non-divisible */
    kinds[count] = OSPREY_PRED_FIELD_OF;
    payloads[count].attached.chunk = field_a;
    payloads[count++].attached.base = make_address(heap, 0);
    kinds[count] = OSPREY_PRED_FIELD_OF;
    payloads[count].attached.chunk = field_b;
    payloads[count++].attached.base = make_address(heap, 0);
    kinds[count] = OSPREY_PRED_FIELD_OF;
    payloads[count].attached.chunk = make_chunk(stack, -8, 8);
    payloads[count++].attached.base = make_address(stack, -16);
    kinds[count] = OSPREY_PRED_POINTER;
    payloads[count].attached.chunk = pointer;
    payloads[count++].attached.base = make_address(heap, 0);

    /* P02-P06 are complete graph inputs, but not decoder families. */
    kinds[count] = OSPREY_PRED_PRIMITIVE_ACCESS;
    payloads[count].prim_access.chunk = primitive;
    payloads[count++].prim_access.insn_pc = 0x44;
    kinds[count] = OSPREY_PRED_UNFOLDABLE_HEAP;
    payloads[count].heap_fold.region = heap;
    payloads[count++].heap_fold.size = 16;
    kinds[count] = OSPREY_PRED_FOLDABLE_HEAP;
    payloads[count].heap_fold.region = heap;
    payloads[count++].heap_fold.size = 0;
    kinds[count] = OSPREY_PRED_HOMO_SEGMENT;
    payloads[count].segment.a1 = make_address(global, 0);
    payloads[count].segment.a2 = make_address(heap, 0);
    payloads[count++].segment.size = 8;
    kinds[count] = OSPREY_PRED_ARRAY_START;
    payloads[count++].addr = make_address(global, 0);

    CHECK(ctx != NULL, "projection context allocated");
    if (ctx == NULL) return NULL;
    add_extent(ctx, stack, -32, 32);
    add_extent(ctx, global, 0, 128);
    add_extent(ctx, heap, 0, 32);
    if (order == 1) {
        for (size_t i = count; i-- > 0;) add_payload(ctx, kinds[i], &payloads[i]);
    } else if (order == 2) {
        static const uint8_t permutation[] = {
            5, 0, 11, 3, 8, 1, 10, 4, 6, 2, 9, 7,
        };
        CHECK(count == G_N_ELEMENTS(permutation),
              "shuffled projection covers every source row");
        for (size_t i = 0; i < count; i++) {
            size_t source = permutation[i];
            add_payload(ctx, kinds[source], &payloads[source]);
        }
    } else {
        for (size_t i = 0; i < count; i++) add_payload(ctx, kinds[i], &payloads[i]);
    }
    set_all_beliefs(ctx, 0.8);
    for (guint i = 0; i < ctx->graph->vars->len; i++) {
        OspreyVar *variable = &g_array_index(ctx->graph->vars, OspreyVar, i);
        variable->direct_support = 3;
        variable->source_rule_bits = UINT64_C(1) << variable->kind;
    }
    return ctx;
}

static void test_valid_projection_and_indexes(void)
{
    OspreyContext *ctx = make_projection_context(false);
    OspreyDecodeInput *input = NULL;
    CHECK(ctx != NULL && build_input(ctx, &input),
          "projection fixture builds canonical input");
    if (input != NULL) {
        CHECK(input->primitive_count == 1 && input->scalar_count == 1 &&
                  input->array_count == 1 && input->field_count == 3 &&
                  input->pointer_count == 1,
              "all projected families retain eligible candidates");
        CHECK(input->discarded_hard_false == 0 &&
                  input->discarded_threshold == 0,
              "valid projection has no discarded candidates");
        CHECK(input->extent_count == 3 && input->extents[0].region.kind ==
                  OSPREY_REGION_GLOBAL,
              "extents are owned and canonically sorted");
        CHECK(input->chunk_range_count == 6 &&
                  input->field_base_range_count == 2 &&
                  input->array_region_range_count == 1 &&
                  input->array_region_stride_range_count == 1,
              "complete chunk/base/region/stride views are built");
        CHECK(input->array_candidates[0].payload.segment.a2.offset == 18,
              "non-divisible graph-valid array reaches Stage 6.3");
        CHECK(input->field_base_ranges[0].count == 2 &&
                  input->field_base_ranges[1].count == 1,
              "base view stores non-contiguous field ordinals as ranges");
        char *dump = dump_input(input);
        CHECK(dump != NULL && strstr(dump, "[posterior-bits") != NULL &&
                  strstr(dump, "[source-rules") != NULL &&
                  strstr(dump, "[extent]") != NULL,
              "input dump contains exact evidence and extents");
        free(dump);
        osprey_decode_input_free(input);
    }
    osprey_free(ctx);
}

static void test_fixed_canonical_dump(void)
{
    static const char expected[] =
        "[discarded-hard-false 0] [discarded-threshold 0]\n"
        "[primitive] [kind 1] [key 0x0000000000564152"
        " 0x0000000000000001 0x0000000000000000"
        " 0x0000000000000001 0x0000000000000002"
        " 0xfffffffffffffff8 0x0000000000000004"
        " 0x0000000000000000 0x0000000000000000"
        " 0x0000000000000000 0x0000000000000000]"
        " [posterior-bits 0x3fe8000000000000] [support 5]"
        " [source-rules 0x0000000000000002]\n"
        "[extent] [region 0] [image 0x0000000000000001]"
        " [site 0x0000000000000002] [lo -16] [hi 0]\n"
        "[chunk-range] [key 0x0000000000564152"
        " 0x0000000000000001 0x0000000000000000"
        " 0x0000000000000001 0x0000000000000002"
        " 0xfffffffffffffff8 0x0000000000000004"
        " 0x0000000000000000 0x0000000000000000"
        " 0x0000000000000000 0x0000000000000000]\n";
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 1, 2);
    uint32_t id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                make_chunk(region, -8, 4));
    set_belief(ctx, id, 0.75);
    OspreyVar *variable = &g_array_index(ctx->graph->vars, OspreyVar, id);
    variable->direct_support = 5;
    variable->source_rule_bits = 2;
    add_extent(ctx, region, -16, 0);
    OspreyDecodeInput *input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_OK && input != NULL,
          "fixed canonical dump fixture builds");
    char *dump = input == NULL ? NULL : dump_input(input);
    CHECK(dump != NULL && strcmp(dump, expected) == 0,
          "canonical dump matches the fixed complete-key record");
    free(dump);
    osprey_decode_input_free(input);
    osprey_free(ctx);
}

static void test_region_identity_collisions(void)
{
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId regions[] = {
        make_region(OSPREY_REGION_STACK_FUNCTION, 1, 2),
        make_region(OSPREY_REGION_STACK_FUNCTION, 1, 3),
        make_region(OSPREY_REGION_STACK_FUNCTION, 2, 2),
    };
    for (size_t i = 0; i < G_N_ELEMENTS(regions); i++) {
        uint32_t id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                    make_chunk(regions[i], -16, 8));
        set_belief(ctx, id, 0.9);
        add_extent(ctx, regions[i], -32, 0);
    }
    OspreyDecodeInput *input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_OK && input != NULL &&
              input->primitive_count == 3 && input->chunk_range_count == 3 &&
              input->extent_count == 3,
          "negative offsets and image/site collisions retain full region identity");
    osprey_decode_input_free(input);
    osprey_free(ctx);
}

static void test_projection_permutation(void)
{
    OspreyContext *left = make_projection_context(0);
    OspreyContext *right = make_projection_context(1);
    OspreyContext *shuffled = make_projection_context(2);
    OspreyDecodeInput *a = NULL;
    OspreyDecodeInput *b = NULL;
    OspreyDecodeInput *c = NULL;
    char *dump_a = NULL;
    char *dump_b = NULL;
    char *dump_c = NULL;
    CHECK(left != NULL && right != NULL && shuffled != NULL &&
              build_input(left, &a) && build_input(right, &b) &&
              build_input(shuffled, &c),
          "forward, reverse, and shuffled graph insertions build");
    if (a != NULL && b != NULL && c != NULL) {
        dump_a = dump_input(a);
        dump_b = dump_input(b);
        dump_c = dump_input(c);
        CHECK(dump_a != NULL && dump_b != NULL && dump_c != NULL &&
                  strcmp(dump_a, dump_b) == 0 &&
                  strcmp(dump_a, dump_c) == 0,
              "canonical input dump ignores graph insertion order");
    }
    free(dump_a);
    free(dump_b);
    free(dump_c);
    osprey_decode_input_free(a);
    osprey_decode_input_free(b);
    osprey_decode_input_free(c);
    osprey_free(left);
    osprey_free(right);
    osprey_free(shuffled);
}

static void test_filter_threshold_and_hard_false(void)
{
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x11, 0x22);
    OspreyChunk low = make_chunk(region, 0, 8);
    OspreyChunk equal = make_chunk(region, 8, 8);
    OspreyVarPayload array_payload;
    uint32_t low_id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, low);
    uint32_t equal_id = add_chunk_var(ctx, OSPREY_PRED_SCALAR, equal);
    memset(&array_payload, 0, sizeof(array_payload));
    array_payload.segment.a1 = make_address(region, 16);
    array_payload.segment.a2 = make_address(region, 24);
    array_payload.segment.size = 8;
    uint32_t array_id = add_payload(ctx, OSPREY_PRED_ARRAY, &array_payload);
    set_belief(ctx, low_id, 0.5999999999999999);
    set_belief(ctx, equal_id, 0.6);
    set_belief(ctx, array_id, 1.0);
    OspreyFactorResult hard = osprey_factor_add_hard_false(
        ctx, OSPREY_RULE_CB06, OSPREY_GRAPH_SECONDARY, array_id);
    CHECK(hard.status == OSPREY_OK, "hard-false factor inserted");
    g_array_index(ctx->graph->vars, OspreyVar, array_id).hard_false = 1;
    OspreyDecodeInput *input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_OK && input != NULL,
          "threshold fixture builds");
    if (input != NULL) {
        CHECK(input->scalar_count == 1 && input->array_count == 0 &&
                  input->primitive_count == 0 && input->discarded_hard_false == 1 &&
                  input->discarded_threshold == 1,
              "hard-false precedes threshold and equality is retained");
        osprey_decode_input_free(input);
    }
    osprey_free(ctx);
}

static void test_graph_boundary_rejections(void)
{
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 1, 2);
    OspreyChunk chunk = make_chunk(region, 0, 8);
    uint32_t id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, chunk);
    set_belief(ctx, id, 0.9);
    add_extent(ctx, region, 0, 8);
    OspreyDecodeInput *input = NULL;

    g_array_free(ctx->graph->factors, TRUE);
    ctx->graph->factors = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "missing factor storage is rejected");
    osprey_free(ctx);

    ctx = new_decode_context();
    id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, chunk);
    set_belief(ctx, id, 0.9);
    add_extent(ctx, region, 0, 8);
    OspreyKey key = osprey_var_key(OSPREY_PRED_PRIMITIVE_VAR,
                                   &(OspreyVarPayload){ .chunk = chunk });
    g_hash_table_remove(ctx->graph->var_index, &key);
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "variable equality index mismatch is rejected");
    osprey_free(ctx);

    ctx = new_decode_context();
    id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, chunk);
    set_belief(ctx, id, 0.9);
    add_extent(ctx, region, 0, 8);
    g_array_index(ctx->graph->vars, OspreyVar, id).belief_valid = 0;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "missing exact belief validity is rejected");
    osprey_free(ctx);

    ctx = new_decode_context();
    id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, chunk);
    set_belief(ctx, id, NAN);
    add_extent(ctx, region, 0, 8);
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "NaN belief is rejected");
    osprey_free(ctx);
}

static void test_exact_belief_boundaries(void)
{
    static const double beliefs[] = {
        0.0, DBL_MIN, 0.6, 1.0,
    };
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 7, 9);
    ctx->config.report_threshold = 0.0;
    for (size_t i = 0; i < G_N_ELEMENTS(beliefs); i++) {
        uint32_t id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                    make_chunk(region, (int64_t)i * 8, 8));
        set_belief(ctx, id, beliefs[i]);
    }
    uint32_t below_id = add_chunk_var(ctx, OSPREY_PRED_SCALAR,
                                      make_chunk(region, 32, 8));
    uint32_t above_id = add_chunk_var(ctx, OSPREY_PRED_SCALAR,
                                      make_chunk(region, 40, 8));
    set_belief(ctx, below_id, nextafter(0.6, 0.0));
    set_belief(ctx, above_id, nextafter(0.6, 1.0));
    add_extent(ctx, region, 0, 48);
    OspreyDecodeInput *input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_OK && input != NULL,
          "exact finite belief boundaries build without clamping");
    if (input != NULL) {
        CHECK(input->primitive_count == G_N_ELEMENTS(beliefs) &&
                  input->scalar_count == 2,
              "zero, DBL_MIN, threshold-adjacent, and one beliefs survive at zero threshold");
        uint64_t zero_bits = UINT64_MAX;
        uint64_t one_bits = 0;
        memcpy(&zero_bits, &input->primitive_candidates[0].posterior,
               sizeof(zero_bits));
        memcpy(&one_bits, &input->primitive_candidates[3].posterior,
               sizeof(one_bits));
        CHECK(input->primitive_candidates[0].posterior_bits == zero_bits &&
                  input->primitive_candidates[3].posterior_bits == one_bits,
              "candidate records preserve exact posterior bits");
        osprey_decode_input_free(input);
    }
    osprey_free(ctx);
}

static void test_invalid_belief_values(void)
{
    const double invalid[] = {
        NAN, INFINITY, -INFINITY, -DBL_MIN, nextafter(1.0, INFINITY),
    };
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 1, 2);
    for (size_t i = 0; i < G_N_ELEMENTS(invalid); i++) {
        OspreyContext *ctx = new_decode_context();
        uint32_t id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                    make_chunk(region, 0, 8));
        set_belief(ctx, id, invalid[i]);
        add_extent(ctx, region, 0, 8);
        OspreyDecodeInput *input = (OspreyDecodeInput *)(uintptr_t)1;
        CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
                  input == NULL,
              "non-finite and out-of-range beliefs are rejected");
        osprey_free(ctx);
    }
}

static void test_variable_identity_rejections(void)
{
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 1, 2);
    OspreyChunk chunk = make_chunk(region, 0, 8);
    OspreyDecodeInput *input = NULL;

    OspreyContext *ctx = new_decode_context();
    uint32_t id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, chunk);
    set_belief(ctx, id, 0.9);
    add_extent(ctx, region, 0, 8);
    g_array_index(ctx->graph->vars, OspreyVar, id).id = id + 1;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "mismatched variable ordinal is rejected");
    osprey_free(ctx);

    ctx = new_decode_context();
    id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, chunk);
    set_belief(ctx, id, 0.9);
    add_extent(ctx, region, 0, 8);
    OspreyVar duplicate = g_array_index(ctx->graph->vars, OspreyVar, id);
    duplicate.id = id + 1;
    g_array_append_val(ctx->graph->vars, duplicate);
    input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "duplicate semantic variable identity is rejected");
    osprey_free(ctx);
}

static void test_hard_false_contract_rejections(void)
{
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 1, 2);
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.segment.a1 = make_address(region, 0);
    payload.segment.a2 = make_address(region, 8);
    payload.segment.size = 8;
    OspreyDecodeInput *input = NULL;

    OspreyContext *ctx = new_decode_context();
    uint32_t array_id = add_payload(ctx, OSPREY_PRED_ARRAY, &payload);
    set_belief(ctx, array_id, 0.9);
    add_extent(ctx, region, 0, 8);
    g_array_index(ctx->graph->vars, OspreyVar, array_id).hard_false = 1;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL,
          "hard-false bit without a factor is rejected");
    osprey_free(ctx);

    ctx = new_decode_context();
    array_id = add_payload(ctx, OSPREY_PRED_ARRAY, &payload);
    set_belief(ctx, array_id, 0.9);
    add_extent(ctx, region, 0, 8);
    CHECK(osprey_factor_add_hard_false(ctx, OSPREY_RULE_CB06,
                                      OSPREY_GRAPH_SECONDARY,
                                      array_id).status == OSPREY_OK,
          "hard-false mismatch fixture factor builds");
    input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL,
          "hard-false factor without the bit is rejected");
    osprey_free(ctx);

    ctx = new_decode_context();
    array_id = add_payload(ctx, OSPREY_PRED_ARRAY, &payload);
    set_belief(ctx, array_id, 0.9);
    add_extent(ctx, region, 0, 8);
    CHECK(osprey_factor_add_hard_false(ctx, OSPREY_RULE_CB06,
                                      OSPREY_GRAPH_SECONDARY,
                                      array_id).status == OSPREY_OK,
          "duplicate hard-false fixture factor builds");
    g_array_index(ctx->graph->vars, OspreyVar, array_id).hard_false = 1;
    OspreyFactor *original = g_array_index(ctx->graph->factors,
                                           OspreyFactor *, 0);
    OspreyFactor *duplicate = g_new0(OspreyFactor, 1);
    *duplicate = *original;
    duplicate->id = 1;
    duplicate->var_ids = g_new(uint32_t, original->num_vars);
    memcpy(duplicate->var_ids, original->var_ids,
           original->num_vars * sizeof(original->var_ids[0]));
    g_array_append_val(ctx->graph->factors, duplicate);
    input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL,
          "duplicate hard-false factor is rejected");
    osprey_free(ctx);

    ctx = new_decode_context();
    uint32_t scalar_id = add_chunk_var(ctx, OSPREY_PRED_SCALAR,
                                       make_chunk(region, 0, 8));
    set_belief(ctx, scalar_id, 0.9);
    add_extent(ctx, region, 0, 8);
    CHECK(osprey_factor_add_hard_false(ctx, OSPREY_RULE_CB06,
                                      OSPREY_GRAPH_SECONDARY,
                                      scalar_id).status == OSPREY_OK,
          "wrong-kind hard-false fixture factor builds");
    input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL,
          "hard-false on a non-array variable is rejected");
    osprey_free(ctx);

    ctx = new_decode_context();
    uint32_t ids[2];
    ids[0] = add_payload(ctx, OSPREY_PRED_ARRAY, &payload);
    ids[1] = add_chunk_var(ctx, OSPREY_PRED_SCALAR,
                           make_chunk(region, 0, 8));
    set_all_beliefs(ctx, 0.9);
    add_extent(ctx, region, 0, 8);
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CB06,
                               OSPREY_GRAPH_SECONDARY,
                               OSPREY_POTENTIAL_IMPLICATION, 1, false,
                               0.8, ids, 2).status == OSPREY_OK,
          "malformed CB06 implication fixture builds");
    input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL,
          "non-hard-false CB06 factor is rejected");
    osprey_free(ctx);
}

static void test_payload_and_extent_rejections(void)
{
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 1, 2);
    OspreyChunk chunk = make_chunk(region, 0, 8);
    uint32_t id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, chunk);
    set_belief(ctx, id, 0.9);
    add_extent(ctx, region, 8, 0);
    OspreyDecodeInput *input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "malformed extent bounds are rejected");
    osprey_free(ctx);

    ctx = new_decode_context();
    id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, chunk);
    set_belief(ctx, id, 0.9);
    add_extent(ctx, region, 0, 8);
    OspreyVarPayload bad;
    memset(&bad, 0, sizeof(bad));
    bad.segment.a1 = make_address(region, 0);
    bad.segment.a2 = make_address(region, 8);
    bad.segment.size = 8;
    OspreyInternResult array = osprey_intern_var(ctx, OSPREY_PRED_ARRAY,
                                                  &bad);
    CHECK(array.id != UINT32_MAX, "payload fixture array inserted");
    set_belief(ctx, array.id, 0.9);
    g_array_index(ctx->graph->vars, OspreyVar, array.id).payload.segment.a2.offset = 0;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "malformed final payload is rejected before projection");
    osprey_free(ctx);

    memset(&bad, 0, sizeof(bad));
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_POINTER, &bad),
          "incomplete attached pointer payload is invalid");
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_PRIMITIVE_VAR, &bad) &&
              !osprey_var_payload_valid(OSPREY_PRED_SCALAR, &bad),
          "zero-width primitive and scalar chunks are invalid");

    bad.prim_access.chunk = make_chunk(region, 0, 0);
    bad.prim_access.insn_pc = 1;
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_PRIMITIVE_ACCESS, &bad),
          "zero-width primitive-access chunk is invalid");

    memset(&bad, 0, sizeof(bad));
    bad.heap_fold.region = region;
    bad.heap_fold.size = 8;
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_UNFOLDABLE_HEAP, &bad) &&
              !osprey_var_payload_valid(OSPREY_PRED_FOLDABLE_HEAP, &bad),
          "heap predicates require a heap-site region");

    memset(&bad, 0, sizeof(bad));
    bad.segment.a1 = make_address(region, 8);
    bad.segment.a2 = make_address(region, 0);
    bad.segment.size = 8;
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_HOMO_SEGMENT, &bad),
          "final homomorphic endpoints must be canonical");
    bad.segment.a1 = make_address(region, 0);
    bad.segment.a2 = make_address(region, 8);
    bad.segment.size = 0;
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_HOMO_SEGMENT, &bad),
          "zero-size homomorphic segment is invalid");

    memset(&bad, 0, sizeof(bad));
    bad.addr = make_address((OspreyRegionId){ .kind = (OspreyRegionKind)99 },
                            0);
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_ARRAY_START, &bad),
          "invalid array-start region kind is rejected");

    memset(&bad, 0, sizeof(bad));
    bad.segment.a1 = make_address(region, 0);
    bad.segment.a2 = make_address(make_region(OSPREY_REGION_GLOBAL, 1, 3), 8);
    bad.segment.size = 8;
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_ARRAY, &bad),
          "array endpoints require complete equal region identity");
    bad.segment.a2 = make_address(region, 8);
    bad.segment.size = 0;
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_ARRAY, &bad),
          "zero-stride array is invalid");
    bad.segment.size = 16;
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_ARRAY, &bad),
          "array span shorter than stride is invalid");

    memset(&bad, 0, sizeof(bad));
    bad.attached.chunk = make_chunk(region, 0, 8);
    bad.attached.base = make_address(make_region(OSPREY_REGION_HEAP_SITE, 0, 4),
                                     0);
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_FIELD_OF, &bad),
          "field chunk and base require one complete region identity");
    bad.attached.base = make_address(region, 8);
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_FIELD_OF, &bad),
          "field base cannot follow its field chunk");
}

static void test_extent_catalog_normalization(void)
{
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId first = make_region(OSPREY_REGION_GLOBAL, 1, 2);
    OspreyRegionId second = make_region(OSPREY_REGION_HEAP_SITE, 3, 4);
    add_extent(ctx, second, -8, 24);
    add_extent(ctx, first, 0, 16);
    OspreyDecodeInput *input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_OK && input != NULL &&
              input->extent_count == 2 &&
              input->extents[0].region.kind == OSPREY_REGION_GLOBAL &&
              input->extents[1].region.kind == OSPREY_REGION_HEAP_SITE,
          "unsorted extents are copied into complete canonical order");
    osprey_decode_input_free(input);
    osprey_free(ctx);

    ctx = new_decode_context();
    add_extent(ctx, first, 0, 8);
    add_extent(ctx, first, 0, 16);
    input = (OspreyDecodeInput *)(uintptr_t)1;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "duplicate complete-region extents are rejected");
    osprey_free(ctx);
}

static void test_unbuilt_extent_catalog_is_rejected(void)
{
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 1, 2);
    uint32_t id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                make_chunk(region, 0, 8));
    set_belief(ctx, id, 0.9);
    add_extent(ctx, region, 0, 8);
    ctx->graph->extents_built = false;
    OspreyDecodeInput *input = (OspreyDecodeInput *)(uintptr_t)1;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "an unfinished extent catalog is rejected");
    osprey_free(ctx);
}

static void test_checked_payload_arithmetic(void)
{
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 1, 2);
    OspreyChunk wrapping = make_chunk(region, INT64_MAX, 1);
    uint32_t id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, wrapping);
    set_belief(ctx, id, 0.9);
    add_extent(ctx, region, INT64_MIN, INT64_MAX);
    OspreyDecodeInput *input = (OspreyDecodeInput *)(uintptr_t)1;
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_PRIMITIVE_VAR,
                                     &(OspreyVarPayload){ .chunk = wrapping }),
          "a chunk with an unrepresentable exclusive end is invalid");
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "decoder rejects unrepresentable chunk arithmetic");
    osprey_free(ctx);

    ctx = new_decode_context();
    OspreyVarPayload heap;
    memset(&heap, 0, sizeof(heap));
    heap.heap_fold.region = make_region(OSPREY_REGION_HEAP_SITE, 0, 3);
    heap.heap_fold.size = (uint64_t)INT64_MAX + 1;
    id = add_payload(ctx, OSPREY_PRED_UNFOLDABLE_HEAP, &heap);
    set_belief(ctx, id, 0.9);
    add_extent(ctx, heap.heap_fold.region, 0, INT64_MAX);
    input = (OspreyDecodeInput *)(uintptr_t)1;
    CHECK(!osprey_var_payload_valid(OSPREY_PRED_UNFOLDABLE_HEAP, &heap),
          "a heap boundary outside the signed canonical domain is invalid");
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "decoder rejects unrepresentable heap arithmetic");
    osprey_free(ctx);
}

static void test_out_of_extent_candidates_are_retained(void)
{
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 1, 2);
    OspreyVarPayload payload;
    uint32_t primitive = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                       make_chunk(region, 64, 8));
    uint32_t scalar = add_chunk_var(ctx, OSPREY_PRED_SCALAR,
                                    make_chunk(region, 72, 8));
    memset(&payload, 0, sizeof(payload));
    payload.segment.a1 = make_address(region, 80);
    payload.segment.a2 = make_address(region, 96);
    payload.segment.size = 8;
    uint32_t array = add_payload(ctx, OSPREY_PRED_ARRAY, &payload);
    memset(&payload, 0, sizeof(payload));
    payload.attached.chunk = make_chunk(region, 104, 8);
    payload.attached.base = make_address(region, 100);
    uint32_t field = add_payload(ctx, OSPREY_PRED_FIELD_OF, &payload);
    memset(&payload, 0, sizeof(payload));
    payload.attached.chunk = make_chunk(region, 112, 4);
    payload.attached.base = make_address(region, 1000);
    uint32_t pointer = add_payload(ctx, OSPREY_PRED_POINTER, &payload);
    set_belief(ctx, primitive, 0.9);
    set_belief(ctx, scalar, 0.9);
    set_belief(ctx, array, 0.9);
    set_belief(ctx, field, 0.9);
    set_belief(ctx, pointer, 0.9);
    add_extent(ctx, region, 0, 8);
    OspreyDecodeInput *input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_OK && input != NULL,
          "Stage 6.1 preserves candidates for later containment validation");
    if (input != NULL) {
        CHECK(input->primitive_count == 1 && input->scalar_count == 1 &&
                  input->array_count == 1 && input->field_count == 1 &&
                  input->pointer_count == 1 &&
                  input->pointer_candidates[0].payload.attached.chunk.size == 4,
              "out-of-extent and wrong-width pointer candidates remain unchanged");
        osprey_decode_input_free(input);
    }
    osprey_free(ctx);
}

static void test_array_region_view_key_order(void)
{
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 1, 2);
    OspreyVarPayload first;
    OspreyVarPayload second;
    memset(&first, 0, sizeof(first));
    memset(&second, 0, sizeof(second));
    first.segment.a1 = make_address(region, 0);
    first.segment.a2 = make_address(region, 16);
    first.segment.size = 8;
    second.segment.a1 = make_address(region, 8);
    second.segment.a2 = make_address(region, 16);
    second.segment.size = 4;
    uint32_t first_id = add_payload(ctx, OSPREY_PRED_ARRAY, &first);
    uint32_t second_id = add_payload(ctx, OSPREY_PRED_ARRAY, &second);
    set_belief(ctx, first_id, 0.9);
    set_belief(ctx, second_id, 0.9);
    add_extent(ctx, region, 0, 32);
    OspreyDecodeInput *input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_OK && input != NULL,
          "two-stride array fixture builds");
    if (input != NULL) {
        CHECK(input->array_count == 2 && input->array_region_range_count == 1 &&
                  input->array_region_ranges[0].count == 2 &&
                  input->array_by_region[0] == 0 &&
                  input->array_by_region[1] == 1,
              "region view uses complete candidate-key order, not stride order");
        CHECK(input->array_region_stride_range_count == 2 &&
                  input->array_by_region_stride[0] == 1 &&
                  input->array_by_region_stride[1] == 0,
              "region-stride view retains stride-first order");
        osprey_decode_input_free(input);
    }
    osprey_free(ctx);
}

static void test_rule_stage_mismatch_is_rejected(void)
{
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 1, 2);
    uint32_t ids[2];
    ids[0] = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                           make_chunk(region, 0, 8));
    ids[1] = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                           make_chunk(region, 8, 8));
    set_all_beliefs(ctx, 0.9);
    add_extent(ctx, region, 0, 16);
    OspreyFactorResult factor = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_SECONDARY,
        OSPREY_POTENTIAL_IMPLICATION, 1, false, 0.8, ids, 2);
    CHECK(factor.status == OSPREY_OK,
          "fixture creates a structurally valid wrong-stage factor");
    OspreyDecodeInput *input = (OspreyDecodeInput *)(uintptr_t)1;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "decoder rejects a rule/factor stage mismatch");
    osprey_free(ctx);
}

static void test_transaction_is_unchanged(void)
{
    OspreyContext *ctx = make_projection_context(false);
    OspreyGraph *graph = ctx->graph;
    OspreyModel *model = ctx->model;
    OspreyModel *staged = ctx->staged_model;
    OspreyStatus tx_status = ctx->tx_status;
    OspreyStatus last_status = ctx->last_status;
    const char *stage = ctx->tx_stage;
    bool ready = ctx->tx_model_ready;
    OspreyDecodeInput *input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_OK,
          "transaction success fixture builds");
    CHECK(ctx->graph == graph && ctx->model == model &&
              ctx->staged_model == staged && ctx->tx_status == tx_status &&
              ctx->last_status == last_status && ctx->tx_stage == stage &&
              ctx->tx_model_ready == ready,
          "successful helper leaves transaction ownership unchanged");
    osprey_decode_input_free(input);
    osprey_free(ctx);
}

static void test_failure_leaves_transaction_unchanged(void)
{
    OspreyContext *ctx = make_projection_context(false);
    OspreyGraph *graph = ctx->graph;
    OspreyModel *model = ctx->model;
    OspreyModel *staged = ctx->staged_model;
    ctx->tx_status = OSPREY_NON_CONVERGED;
    ctx->tx_stage = "secondary";
    ctx->tx_reason = "fixture";
    ctx->tx_model_ready = true;
    ctx->last_status = OSPREY_GRAPH_ARITHMETIC;
    ctx->last_analyze_time_ms = 77;
    ctx->last_exact_logz = 3.25;
    uint64_t total_samples = ctx->total_samples;
    uint64_t observations = ctx->total_dynamic_observations;
    OspreyDecodeInput *input = (OspreyDecodeInput *)(uintptr_t)1;
    osprey_decode_test_set_alloc_fail_after(0);
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "injected decoder allocation failure returns no input");
    osprey_decode_test_set_alloc_fail_after(-1);
    CHECK(ctx->graph == graph && ctx->model == model &&
              ctx->staged_model == staged &&
              ctx->tx_status == OSPREY_NON_CONVERGED &&
              strcmp(ctx->tx_stage, "secondary") == 0 &&
              strcmp(ctx->tx_reason, "fixture") == 0 &&
              ctx->tx_model_ready &&
              ctx->last_status == OSPREY_GRAPH_ARITHMETIC &&
              ctx->last_analyze_time_ms == 77 &&
              ctx->last_exact_logz == 3.25 &&
              ctx->total_samples == total_samples &&
              ctx->total_dynamic_observations == observations,
          "decoder failure leaves graph/model/transaction diagnostics unchanged");
    osprey_free(ctx);
}

static void test_input_owns_source_data(void)
{
    OspreyContext *ctx = make_projection_context(false);
    OspreyDecodeInput *input = NULL;
    CHECK(ctx != NULL && osprey_decode_input_build(ctx, &input) == OSPREY_OK &&
              input != NULL,
          "ownership fixture builds");
    char *before = input == NULL ? NULL : dump_input(input);
    osprey_free(ctx);
    char *after = input == NULL ? NULL : dump_input(input);
    CHECK(before != NULL && after != NULL && strcmp(before, after) == 0,
          "decoder input remains complete after source graph teardown");
    free(before);
    free(after);
    osprey_decode_input_free(input);
}

static void test_null_and_missing_inputs(void)
{
    OspreyDecodeInput *input = (OspreyDecodeInput *)(uintptr_t)1;
    CHECK(osprey_decode_input_build(NULL, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "NULL context is rejected and clears output");

    OspreyContext *ctx = new_decode_context();
    CHECK(osprey_decode_input_build(ctx, NULL) == OSPREY_INVALID_MODEL,
          "NULL output pointer is rejected");
    OspreyGraph *graph = ctx->graph;
    ctx->graph = NULL;
    input = (OspreyDecodeInput *)(uintptr_t)1;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "missing graph is rejected");
    osprey_graph_free(graph);
    osprey_free(ctx);

    ctx = new_decode_context();
    GArray *vars = ctx->graph->vars;
    ctx->graph->vars = NULL;
    input = (OspreyDecodeInput *)(uintptr_t)1;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "missing variable storage is rejected");
    ctx->graph->vars = vars;
    osprey_free(ctx);

    ctx = new_decode_context();
    GArray *extents = ctx->graph->extents;
    ctx->graph->extents = NULL;
    input = (OspreyDecodeInput *)(uintptr_t)1;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "missing extent storage is rejected");
    ctx->graph->extents = extents;
    osprey_free(ctx);
}

static void test_repeated_build_and_free(void)
{
    OspreyContext *ctx = make_projection_context(false);
    char *reference = NULL;
    for (unsigned i = 0; i < 4; i++) {
        OspreyDecodeInput *input = NULL;
        CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_OK &&
                  input != NULL,
              "repeated decoder input build succeeds");
        char *dump = input == NULL ? NULL : dump_input(input);
        if (i == 0) {
            reference = dump;
        } else {
            CHECK(reference != NULL && dump != NULL &&
                      strcmp(reference, dump) == 0,
                  "repeated builds remain byte-identical");
            free(dump);
        }
        osprey_decode_input_free(input);
    }
    free(reference);
    osprey_free(ctx);
}

static void test_count_and_limit_boundaries(void)
{
    OspreyContext *ctx = new_decode_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 1, 2);
    uint32_t id = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                make_chunk(region, 0, 8));
    set_belief(ctx, id, 0.9);
    add_extent(ctx, region, 0, 8);
    ctx->config.max_variables = 0;
    OspreyDecodeInput *input = (OspreyDecodeInput *)(uintptr_t)1;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "source variable count above the accepted bound is rejected");
    osprey_free(ctx);

    ctx = new_decode_context();
    uint32_t ids[2];
    ids[0] = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                           make_chunk(region, 0, 8));
    ids[1] = add_chunk_var(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                           make_chunk(region, 8, 8));
    set_all_beliefs(ctx, 0.9);
    add_extent(ctx, region, 0, 16);
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CA02,
                               OSPREY_GRAPH_BASE_CA,
                               OSPREY_POTENTIAL_IMPLICATION, 1, false,
                               0.8, ids, 2).status == OSPREY_OK,
          "factor-bound fixture builds");
    ctx->config.max_factors = 0;
    input = (OspreyDecodeInput *)(uintptr_t)1;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_INVALID_MODEL &&
              input == NULL,
          "source factor count above the accepted bound is rejected");
    osprey_free(ctx);

    ctx = new_decode_context();
    input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_OK && input != NULL &&
              input->primitive_count == 0 && input->chunk_candidate_count == 0 &&
              input->extent_count == 0,
          "zero-count arrays and indexes require no sentinel allocation");
    osprey_decode_input_free(input);
    osprey_free(ctx);
}

static void test_allocation_failures(void)
{
    OspreyContext *ctx = make_projection_context(false);
    bool saw_success = false;
    for (int64_t failure = 0; failure < 64; failure++) {
        OspreyDecodeInput *input = (OspreyDecodeInput *)(uintptr_t)1;
        osprey_decode_test_set_alloc_fail_after(failure);
        OspreyStatus status = osprey_decode_input_build(ctx, &input);
        if (status == OSPREY_OK) {
            CHECK(input != NULL, "allocation hook success returns input");
            osprey_decode_input_free(input);
            saw_success = true;
            break;
        }
        CHECK(status == OSPREY_INVALID_MODEL && input == NULL,
              "allocation failure returns no partial input");
    }
    osprey_decode_test_set_alloc_fail_after(-1);
    CHECK(saw_success, "allocation-failure sweep reaches normal allocation");
    OspreyDecodeInput *input = NULL;
    CHECK(osprey_decode_input_build(ctx, &input) == OSPREY_OK && input != NULL,
          "success after allocation failure remains possible");
    osprey_decode_input_free(input);
    osprey_free(ctx);
}

static void test_threshold_configuration(void)
{
    const char *saved = g_getenv("BINRADAR_OSPREY_REPORT_THRESHOLD");
    char *copy = saved == NULL ? NULL : g_strdup(saved);
    OspreyConfig config;
    g_unsetenv("BINRADAR_OSPREY_REPORT_THRESHOLD");
    CHECK(osprey_config_from_env(&config) && config.report_threshold == 0.6,
          "report threshold defaults to 0.6");
    const char *valid[] = {
        "0", "-0", "0.6", "1", "2.2250738585072014e-308",
    };
    for (size_t i = 0; i < G_N_ELEMENTS(valid); i++) {
        g_setenv("BINRADAR_OSPREY_REPORT_THRESHOLD", valid[i], TRUE);
        CHECK(osprey_config_from_env(&config) &&
                  isfinite(config.report_threshold) &&
                  config.report_threshold >= 0.0 &&
                  config.report_threshold <= 1.0,
              "report threshold accepts finite boundary strings");
    }
    const char *invalid[] = {
        "nan", "+nan", "inf", "+inf", "-inf", "-0.1", "1.1",
        "garbage", "0.5x", "1e-9999",
    };
    for (size_t i = 0; i < G_N_ELEMENTS(invalid); i++) {
        g_setenv("BINRADAR_OSPREY_REPORT_THRESHOLD", invalid[i], TRUE);
        CHECK(!osprey_config_from_env(&config),
              "report threshold rejects malformed or nonfinite input");
    }
    if (copy != NULL) g_setenv("BINRADAR_OSPREY_REPORT_THRESHOLD", copy, TRUE);
    else g_unsetenv("BINRADAR_OSPREY_REPORT_THRESHOLD");
    g_free(copy);
}

int main(void)
{
    RUN(test_valid_projection_and_indexes);
    RUN(test_fixed_canonical_dump);
    RUN(test_region_identity_collisions);
    RUN(test_projection_permutation);
    RUN(test_filter_threshold_and_hard_false);
    RUN(test_graph_boundary_rejections);
    RUN(test_exact_belief_boundaries);
    RUN(test_invalid_belief_values);
    RUN(test_variable_identity_rejections);
    RUN(test_hard_false_contract_rejections);
    RUN(test_payload_and_extent_rejections);
    RUN(test_extent_catalog_normalization);
    RUN(test_unbuilt_extent_catalog_is_rejected);
    RUN(test_checked_payload_arithmetic);
    RUN(test_out_of_extent_candidates_are_retained);
    RUN(test_array_region_view_key_order);
    RUN(test_rule_stage_mismatch_is_rejected);
    RUN(test_transaction_is_unchanged);
    RUN(test_failure_leaves_transaction_unchanged);
    RUN(test_input_owns_source_data);
    RUN(test_null_and_missing_inputs);
    RUN(test_repeated_build_and_free);
    RUN(test_count_and_limit_boundaries);
    RUN(test_allocation_failures);
    RUN(test_threshold_configuration);
    fprintf(stderr, "stage6.1: %u/%u tests passed\n", executed - failures,
            registered);
    return failures == 0 ? 0 : 1;
}
