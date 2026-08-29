/* Stage 3.2 predicate, candidate, and factor foundation tests. */

#include "osprey.h"
#include "osprey-internal.h"

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

static OspreyConfig graph_config(void)
{
    OspreyConfig config;
    memset(&config, 0, sizeof(config));
    config.enabled = true;
    config.shared_bytes = 1u << 20;
    config.max_facts = 1024;
    config.max_chunks_per_region = 128;
    config.max_candidates_per_kind_region = 4096;
    config.max_variables = 1024;
    config.max_factors = 1024;
    config.max_exact_clique_vars = 20;
    config.report_threshold = 0.5;
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

static OspreyContext *new_graph_context(const OspreyConfig *config)
{
    OspreyContext *ctx = osprey_new(config);
    ctx->graph = osprey_graph_new();
    return ctx;
}

static OspreyInternResult add_var(OspreyContext *ctx, uint8_t kind,
                                  const OspreyChunk *chunk)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.chunk = *chunk;
    return osprey_intern_var(ctx, kind, &payload);
}

static void add_access(OspreyContext *ctx, uint64_t pc,
                       const OspreyChunk *chunk)
{
    OspreyAccessFact fact;
    memset(&fact, 0, sizeof(fact));
    fact.pc = pc;
    fact.chunk = *chunk;
    fact.dynamic_count = 1;
    fact.sample_support = 1;
    g_array_append_val(ctx->access_facts, fact);
}

static OspreyKindRegionCount *bucket_count(OspreyGraph *graph, uint8_t kind,
                                           const OspreyRegionId *region)
{
    OspreyKey key = osprey_kind_region_key(kind, region);
    return g_hash_table_lookup(graph->kind_region, &key);
}

static double exp_weight(const OspreyFactor *factor, const uint8_t *assignment)
{
    double log_weight = 0.0;
    CHECK(osprey_factor_log_weight(factor, assignment, &log_weight),
          "factor evaluator accepts valid factor");
    return isinf(log_weight) && log_weight < 0.0 ? 0.0 : exp(log_weight);
}

static void test_predicate_identity(void)
{
    OspreyConfig config = graph_config();
    OspreyContext *ctx = new_graph_context(&config);
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyRegionId heap_a = make_region(OSPREY_REGION_HEAP_SITE, 0x100);
    OspreyRegionId heap_b = make_region(OSPREY_REGION_HEAP_SITE, 0x200);
    OspreyChunk chunk = make_chunk(global, 8, 8);

    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.chunk = chunk;
    OspreyInternResult a = osprey_intern_var(ctx,
                                             OSPREY_PRED_PRIMITIVE_VAR,
                                             &payload);
    OspreyVarPayload noisy;
    memset(&noisy, 0xa5, sizeof(noisy));
    noisy.chunk = chunk;
    OspreyInternResult duplicate = osprey_intern_var(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, &noisy);
    CHECK(a.inserted && duplicate.id == a.id && !duplicate.inserted,
          "inactive union bytes do not change primitive identity");

    memset(&payload, 0, sizeof(payload));
    payload.prim_access.chunk = chunk;
    payload.prim_access.insn_pc = 0x123;
    OspreyInternResult access = osprey_intern_var(
        ctx, OSPREY_PRED_PRIMITIVE_ACCESS, &payload);
    CHECK(access.inserted, "primitive access identity");
    memset(&payload, 0, sizeof(payload));
    payload.chunk = chunk;
    CHECK(osprey_intern_var(ctx, OSPREY_PRED_SCALAR, &payload).inserted,
          "scalar identity");

    memset(&payload, 0, sizeof(payload));
    payload.heap_fold.region = heap_a;
    payload.heap_fold.size = 16;
    CHECK(osprey_intern_var(ctx, OSPREY_PRED_UNFOLDABLE_HEAP,
                            &payload).inserted, "unfoldable identity");
    CHECK(osprey_intern_var(ctx, OSPREY_PRED_FOLDABLE_HEAP,
                            &payload).inserted, "foldable identity");

    memset(&payload, 0, sizeof(payload));
    payload.segment.a1 = make_address(global, 0);
    payload.segment.a2 = make_address(heap_a, 0);
    payload.segment.size = 8;
    OspreyInternResult segment = osprey_intern_var(
        ctx, OSPREY_PRED_HOMO_SEGMENT, &payload);
    payload.segment.a1 = make_address(heap_a, 0);
    payload.segment.a2 = make_address(global, 0);
    OspreyInternResult segment_reverse = osprey_intern_var(
        ctx, OSPREY_PRED_HOMO_SEGMENT, &payload);
    CHECK(segment.inserted && segment_reverse.id == segment.id &&
          !segment_reverse.inserted, "HomoSegment endpoint reversal canonicalized");

    memset(&payload, 0, sizeof(payload));
    payload.segment.a1 = make_address(global, 0);
    payload.segment.a2 = make_address(global, 16);
    payload.segment.size = 8;
    CHECK(osprey_intern_var(ctx, OSPREY_PRED_ARRAY, &payload).inserted,
          "half-open array identity");

    memset(&payload, 0, sizeof(payload));
    payload.addr = make_address(global, 0);
    CHECK(osprey_intern_var(ctx, OSPREY_PRED_ARRAY_START, &payload).inserted,
          "array start identity");

    memset(&payload, 0, sizeof(payload));
    payload.attached.chunk = chunk;
    payload.attached.base = make_address(heap_a, 0);
    OspreyInternResult field_a = osprey_intern_var(
        ctx, OSPREY_PRED_FIELD_OF, &payload);
    payload.attached.base = make_address(heap_b, 0);
    OspreyInternResult field_b = osprey_intern_var(
        ctx, OSPREY_PRED_FIELD_OF, &payload);
    CHECK(field_a.inserted && field_b.inserted && field_a.id != field_b.id,
          "FieldOf target region is part of identity");
    payload.attached.base = make_address(heap_a, 0);
    OspreyInternResult pointer_a = osprey_intern_var(
        ctx, OSPREY_PRED_POINTER, &payload);
    payload.attached.base = make_address(heap_b, 0);
    OspreyInternResult pointer_b = osprey_intern_var(
        ctx, OSPREY_PRED_POINTER, &payload);
    CHECK(pointer_a.inserted && pointer_b.inserted && pointer_a.id != pointer_b.id,
          "Pointer target region is part of identity");

    CHECK(ctx->graph->vars->len == 12, "all ten predicate families retain identity");

    OspreyChunk invalid_chunk = chunk;
    invalid_chunk.address.region.kind = (OspreyRegionKind)-1;
    memset(&payload, 0, sizeof(payload));
    payload.chunk = invalid_chunk;
    CHECK(osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                            &payload).id == UINT32_MAX,
          "negative region kind is rejected");
    osprey_free(ctx);
}

static void test_candidate_selection_and_caps(void)
{
    OspreyConfig config = graph_config();
    config.max_candidates_per_kind_region = 2;
    OspreyContext *ctx = new_graph_context(&config);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk c0 = make_chunk(region, 0, 8);
    OspreyChunk c1 = make_chunk(region, 8, 8);
    OspreyChunk c2 = make_chunk(region, 16, 8);
    add_access(ctx, 1, &c0);
    add_access(ctx, 1, &c1);
    add_access(ctx, 1, &c2);

    OspreyCandidateProposal proposals[4];
    memset(proposals, 0, sizeof(proposals));
    proposals[0].predicate_kind = OSPREY_PRED_PRIMITIVE_VAR;
    proposals[0].payload.chunk = c2;
    proposals[0].direct_support = 4;
    proposals[0].prior = 0.4;
    proposals[0].source_rule = OSPREY_RULE_CA01;
    proposals[1] = proposals[0];
    proposals[1].payload.chunk = c0;
    proposals[1].direct_support = 1;
    proposals[1].prior = 0.99;
    proposals[2] = proposals[0];
    proposals[2].payload.chunk = c1;
    proposals[2].direct_support = 3;
    proposals[2].prior = 0.2;
    proposals[3] = proposals[2];
    proposals[3].direct_support = 6;
    proposals[3].source_rule = OSPREY_RULE_CA02;

    OspreyStatus status = osprey_candidate_select(ctx, proposals,
                                                  G_N_ELEMENTS(proposals));
    CHECK(status == OSPREY_LIMIT_EXCEEDED, "candidate cap is reported");
    CHECK(ctx->graph->vars->len == 2, "candidate cap retains deterministic prefix");
    CHECK(g_array_index(ctx->graph->vars, OspreyVar, 0).payload.chunk.address.offset == 8 &&
          g_array_index(ctx->graph->vars, OspreyVar, 1).payload.chunk.address.offset == 16,
          "candidate ranking uses merged support before prior");
    const OspreyVar *merged = &g_array_index(ctx->graph->vars, OspreyVar, 0);
    CHECK(merged->direct_support == 9 && merged->prior == 0.2 &&
          merged->source_rule_bits == ((1ULL << OSPREY_RULE_CA01) |
                                       (1ULL << OSPREY_RULE_CA02)),
          "candidate diagnostics retain merged support, prior, and sources");
    OspreyKindRegionCount *counts = bucket_count(ctx->graph,
                                                  OSPREY_PRED_PRIMITIVE_VAR,
                                                  &region);
    CHECK(counts != NULL && counts->kept == 2 && counts->dropped == 1,
          "candidate accounting counts unique kept and dropped keys");

    OspreyCandidateProposal duplicate = proposals[3];
    status = osprey_candidate_select(ctx, &duplicate, 1);
    CHECK(status == OSPREY_OK && ctx->graph->vars->len == 2,
          "duplicate remains usable at a full bucket");
    osprey_free(ctx);

    config = graph_config();
    config.max_candidates_per_kind_region = 1;
    ctx = new_graph_context(&config);
    OspreyChunk negative = make_chunk(region, -8, 8);
    add_access(ctx, 1, &negative);
    add_access(ctx, 2, &c0);
    OspreyCandidateProposal signed_order[2];
    memset(signed_order, 0, sizeof(signed_order));
    signed_order[0].predicate_kind = OSPREY_PRED_PRIMITIVE_VAR;
    signed_order[0].payload.chunk = c0;
    signed_order[0].direct_support = 1;
    signed_order[0].prior = 0.8;
    signed_order[0].source_rule = OSPREY_RULE_CA01;
    signed_order[1] = signed_order[0];
    signed_order[1].payload.chunk = negative;
    status = osprey_candidate_select(ctx, signed_order,
                                     G_N_ELEMENTS(signed_order));
    CHECK(status == OSPREY_LIMIT_EXCEEDED && ctx->graph->vars->len == 1 &&
          g_array_index(ctx->graph->vars, OspreyVar, 0)
                  .payload.chunk.address.offset == -8,
          "candidate key tie-break uses signed canonical offsets");
    osprey_free(ctx);

    config = graph_config();
    config.max_variables = 1;
    ctx = new_graph_context(&config);
    add_access(ctx, 1, &c0);
    add_access(ctx, 2, &c1);
    OspreyInternResult seeded = add_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &c0);
    CHECK(seeded.inserted, "global-cap seed variable inserted");
    OspreyCandidateProposal global_cap[2];
    memset(global_cap, 0, sizeof(global_cap));
    global_cap[0].predicate_kind = OSPREY_PRED_PRIMITIVE_VAR;
    global_cap[0].payload.chunk = c0;
    global_cap[0].direct_support = 2;
    global_cap[0].prior = 0.8;
    global_cap[0].source_rule = OSPREY_RULE_CA01;
    global_cap[1] = global_cap[0];
    global_cap[1].payload.chunk = c1;
    status = osprey_candidate_select(ctx, global_cap,
                                     G_N_ELEMENTS(global_cap));
    counts = bucket_count(ctx->graph, OSPREY_PRED_PRIMITIVE_VAR, &region);
    const OspreyVar *seed_var = &g_array_index(ctx->graph->vars, OspreyVar,
                                               seeded.id);
    CHECK(status == OSPREY_LIMIT_EXCEEDED && ctx->graph->vars->len == 1 &&
          seed_var->direct_support == 0 && seed_var->source_rule_bits == 0,
          "global variable-cap rejection leaves variables and evidence atomic");
    CHECK(counts != NULL && counts->kept == 0 && counts->dropped == 1 &&
          ctx->graph->limit_rows == 1,
          "global variable-cap rejection reports exact new-candidate drops");
    osprey_free(ctx);
}

static void test_candidate_permutations(void)
{
    static const unsigned permutations[6][3] = {
        { 0, 1, 2 }, { 0, 2, 1 }, { 1, 0, 2 },
        { 1, 2, 0 }, { 2, 0, 1 }, { 2, 1, 0 },
    };
    OspreyConfig config = graph_config();
    config.max_candidates_per_kind_region = 2;
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk chunks[3] = {
        make_chunk(region, -8, 8), make_chunk(region, 0, 8),
        make_chunk(region, 8, 8),
    };

    for (unsigned p = 0; p < G_N_ELEMENTS(permutations); p++) {
        OspreyContext *ctx = new_graph_context(&config);
        OspreyCandidateProposal proposals[3];
        memset(proposals, 0, sizeof(proposals));
        for (unsigned i = 0; i < G_N_ELEMENTS(chunks); i++) {
            add_access(ctx, i + 1, &chunks[i]);
            unsigned source = permutations[p][i];
            proposals[i].predicate_kind = OSPREY_PRED_PRIMITIVE_VAR;
            proposals[i].payload.chunk = chunks[source];
            proposals[i].direct_support = source == 2 ? 2 : 1;
            proposals[i].prior = 0.5;
            proposals[i].source_rule = OSPREY_RULE_CA01;
        }
        CHECK(osprey_candidate_select(ctx, proposals,
                                      G_N_ELEMENTS(proposals)) ==
                  OSPREY_LIMIT_EXCEEDED,
              "permuted candidate set reaches the same cap");
        CHECK(ctx->graph->vars->len == 2 &&
              g_array_index(ctx->graph->vars, OspreyVar, 0)
                      .payload.chunk.address.offset == 8 &&
              g_array_index(ctx->graph->vars, OspreyVar, 1)
                      .payload.chunk.address.offset == -8,
              "candidate support and signed-key ranking ignore input order");
        osprey_free(ctx);
    }
}

static void test_candidate_extent_validation(void)
{
    OspreyConfig config = graph_config();
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyRegionId heap = make_region(OSPREY_REGION_HEAP_SITE, 0x100);
    OspreyContext *ctx = new_graph_context(&config);
    OspreyChunk g0 = make_chunk(global, 0, 8);
    OspreyChunk g1 = make_chunk(global, 8, 8);
    OspreyChunk h0 = make_chunk(heap, 0, 8);
    add_access(ctx, 1, &g0);
    add_access(ctx, 2, &g1);
    add_access(ctx, 3, &h0);
    OspreyMallocFact alloc;
    memset(&alloc, 0, sizeof(alloc));
    alloc.site_pc = heap.site_offset;
    alloc.requested_size = 16;
    alloc.sample_support = 1;
    g_array_append_val(ctx->alloc_facts, alloc);

    OspreyCandidateProposal homo;
    memset(&homo, 0, sizeof(homo));
    homo.predicate_kind = OSPREY_PRED_HOMO_SEGMENT;
    homo.payload.segment.a1 = g0.address;
    homo.payload.segment.a2 = h0.address;
    homo.payload.segment.size = 8;
    homo.prior = 0.8;
    homo.source_rule = OSPREY_RULE_CD01;
    CHECK(osprey_candidate_select(ctx, &homo, 1) == OSPREY_OK,
          "HomoSegment validates both endpoint extents and starts");
    osprey_free(ctx);

    ctx = new_graph_context(&config);
    add_access(ctx, 1, &g0);
    OspreyCandidateProposal bad_array;
    memset(&bad_array, 0, sizeof(bad_array));
    bad_array.predicate_kind = OSPREY_PRED_ARRAY;
    bad_array.payload.segment.a1 = g0.address;
    bad_array.payload.segment.a2 = make_address(global, 8);
    bad_array.payload.segment.size = 16;
    bad_array.prior = 0.8;
    bad_array.source_rule = OSPREY_RULE_CB02;
    CHECK(osprey_candidate_select(ctx, &bad_array, 1) == OSPREY_INVALID_GRAPH,
          "array shorter than one stride is rejected");
    osprey_free(ctx);

    ctx = new_graph_context(&config);
    add_access(ctx, 1, &g0);
    bad_array.payload.segment.a2 = make_address(global, 16);
    CHECK(osprey_candidate_select(ctx, &bad_array, 1) == OSPREY_INVALID_GRAPH,
          "array outside observed extent is rejected");
    osprey_free(ctx);

    ctx = new_graph_context(&config);
    alloc.requested_size = 0;
    g_array_append_val(ctx->alloc_facts, alloc);
    OspreyCandidateProposal zero_tail;
    memset(&zero_tail, 0, sizeof(zero_tail));
    zero_tail.predicate_kind = OSPREY_PRED_FOLDABLE_HEAP;
    zero_tail.payload.heap_fold.region = heap;
    zero_tail.payload.heap_fold.size = 0;
    zero_tail.prior = 0.8;
    zero_tail.source_rule = OSPREY_RULE_CC01;
    CHECK(osprey_candidate_select(ctx, &zero_tail, 1) == OSPREY_OK,
          "zero-size heap extent is explicit and valid for zero tail");
    osprey_free(ctx);

    ctx = new_graph_context(&config);
    OspreyChunk low = make_chunk(global, INT64_MIN, 1);
    OspreyChunk high = make_chunk(global, INT64_MAX - 1, 1);
    add_access(ctx, 1, &low);
    add_access(ctx, 2, &high);
    OspreyCandidateProposal field;
    memset(&field, 0, sizeof(field));
    field.predicate_kind = OSPREY_PRED_FIELD_OF;
    field.payload.attached.chunk = high;
    field.payload.attached.base = make_address(global, INT64_MIN);
    field.prior = 0.8;
    field.source_rule = OSPREY_RULE_CD06;
    CHECK(osprey_candidate_select(ctx, &field, 1) == OSPREY_INVALID_GRAPH,
          "field-relative subtraction overflow is rejected");
    osprey_free(ctx);

    ctx = new_graph_context(&config);
    add_access(ctx, 1, &g0);
    OspreyCandidateProposal end_start;
    memset(&end_start, 0, sizeof(end_start));
    end_start.predicate_kind = OSPREY_PRED_ARRAY_START;
    end_start.payload.addr = make_address(global, 8);
    end_start.prior = 0.8;
    end_start.source_rule = OSPREY_RULE_CB08;
    CHECK(osprey_candidate_select(ctx, &end_start, 1) == OSPREY_INVALID_GRAPH,
          "array start rejects the exclusive region end");
    osprey_free(ctx);

    ctx = new_graph_context(&config);
    add_access(ctx, 1, &g0);
    OspreyCandidateProposal pointer;
    memset(&pointer, 0, sizeof(pointer));
    pointer.predicate_kind = OSPREY_PRED_POINTER;
    pointer.payload.attached.chunk = g0;
    pointer.payload.attached.base = make_address(heap, 0);
    pointer.prior = 0.8;
    pointer.source_rule = OSPREY_RULE_CD11;
    CHECK(osprey_candidate_select(ctx, &pointer, 1) == OSPREY_INVALID_GRAPH,
          "pointer target requires a modeled canonical address");
    osprey_free(ctx);
}

static void test_factor_potentials_and_validation(void)
{
    OspreyConfig config = graph_config();
    OspreyContext *ctx = new_graph_context(&config);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk chunks[5];
    for (unsigned i = 0; i < G_N_ELEMENTS(chunks); i++) {
        chunks[i] = make_chunk(region, (int64_t)i * 8, 8);
        CHECK(add_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &chunks[i]).inserted,
              "factor test variable inserted");
    }

    uint32_t one[1] = { 0 };
    OspreyFactorResult prior = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
        OSPREY_POTENTIAL_PRIOR, 0, false, 0.8, one, 1);
    CHECK(prior.status == OSPREY_OK && prior.inserted,
          "positive unary prior inserted");
    uint8_t a0[1] = { 0 }, a1[1] = { 1 };
    CHECK(fabs(exp_weight(g_array_index(ctx->graph->factors,
                                       OspreyFactor *, prior.id), a0) - 0.2) < 1e-12 &&
          fabs(exp_weight(g_array_index(ctx->graph->factors,
                                       OspreyFactor *, prior.id), a1) - 0.8) < 1e-12,
          "positive unary prior table");

    OspreyFactorResult negative_prior = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA08, OSPREY_GRAPH_BASE_CA,
        OSPREY_POTENTIAL_PRIOR, 0, true, 0.2, one, 1);
    CHECK(negative_prior.status == OSPREY_OK,
          "negative unary prior inserted");
    CHECK(fabs(exp_weight(g_array_index(ctx->graph->factors,
                                       OspreyFactor *, negative_prior.id), a0) - 0.8) < 1e-12 &&
          fabs(exp_weight(g_array_index(ctx->graph->factors,
                                       OspreyFactor *, negative_prior.id), a1) - 0.2) < 1e-12,
          "negative unary prior mirrors target-true probability");

    uint32_t implication_ids[2] = { 0, 1 };
    OspreyFactorResult implication = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA04, OSPREY_GRAPH_BASE_CA,
        OSPREY_POTENTIAL_IMPLICATION, 1, false, 0.8, implication_ids, 2);
    CHECK(implication.status == OSPREY_OK, "positive implication inserted");
    OspreyFactor *positive = g_array_index(ctx->graph->factors,
                                           OspreyFactor *, implication.id);
    uint8_t pp00[2] = { 0, 0 }, pp01[2] = { 0, 1 };
    uint8_t pp10[2] = { 1, 0 }, pp11[2] = { 1, 1 };
    CHECK(fabs(exp_weight(positive, pp00) - 0.8) < 1e-12 &&
          fabs(exp_weight(positive, pp01) - 0.8) < 1e-12 &&
          fabs(exp_weight(positive, pp10) - 0.2) < 1e-12 &&
          fabs(exp_weight(positive, pp11) - 0.8) < 1e-12,
          "published positive implication table");

    OspreyFactorResult negative = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA03, OSPREY_GRAPH_BASE_CA,
        OSPREY_POTENTIAL_IMPLICATION, 1, true, 0.2, implication_ids, 2);
    OspreyFactor *negative_factor = g_array_index(ctx->graph->factors,
                                                  OspreyFactor *, negative.id);
    CHECK(fabs(exp_weight(negative_factor, pp00) - 0.8) < 1e-12 &&
          fabs(exp_weight(negative_factor, pp01) - 0.8) < 1e-12 &&
          fabs(exp_weight(negative_factor, pp10) - 0.8) < 1e-12 &&
          fabs(exp_weight(negative_factor, pp11) - 0.2) < 1e-12,
          "mirrored negative implication table");

    uint32_t conjunction_ids[3] = { 0, 1, 2 };
    OspreyFactorResult conjunction = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CD08, OSPREY_GRAPH_SECONDARY,
        OSPREY_POTENTIAL_IMPLICATION, 2, false, 0.8, conjunction_ids, 3);
    uint8_t cp001[3] = { 1, 1, 0 }, cp011[3] = { 1, 0, 1 }, cp111[3] = { 1, 1, 1 };
    OspreyFactor *conjunction_factor = g_array_index(
        ctx->graph->factors, OspreyFactor *, conjunction.id);
    CHECK(conjunction.status == OSPREY_OK &&
          fabs(exp_weight(conjunction_factor, cp001) - 0.2) < 1e-12 &&
          fabs(exp_weight(conjunction_factor, cp011) - 0.8) < 1e-12 &&
          fabs(exp_weight(conjunction_factor, cp111) - 0.8) < 1e-12,
          "multi-antecedent implication table");
    uint8_t cp110[3] = { 1, 1, 0 };
    CHECK(fabs(exp_weight(conjunction_factor, cp110) - 0.2) < 1e-12,
          "multi-antecedent violated assignment");

    uint32_t hard_id[1] = { 3 };
    OspreyFactorResult hard = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CB06, OSPREY_GRAPH_SECONDARY,
        OSPREY_POTENTIAL_HARD_FALSE, UINT16_MAX, false, 0.0, hard_id, 1);
    OspreyFactor *hard_factor = g_array_index(ctx->graph->factors,
                                              OspreyFactor *, hard.id);
    uint8_t hf0[1] = { 0 }, hf1[1] = { 1 };
    CHECK(hard.status == OSPREY_OK && exp_weight(hard_factor, hf0) == 1.0 &&
          exp_weight(hard_factor, hf1) == 0.0,
          "hard false potential table");

    uint32_t reverse_ids[2] = { 1, 0 };
    OspreyFactorResult reverse = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
        OSPREY_POTENTIAL_IMPLICATION, 1, false, 0.8, reverse_ids, 2);
    OspreyFactorResult reverse_duplicate = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
        OSPREY_POTENTIAL_IMPLICATION, 1, false, 0.8, reverse_ids, 2);
    CHECK(reverse.status == OSPREY_OK && reverse.inserted &&
          reverse_duplicate.id == reverse.id && !reverse_duplicate.inserted,
          "semantic ordered duplicate factor identity");
    OspreyFactorResult ordered = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
        OSPREY_POTENTIAL_IMPLICATION, 1, false, 0.8, implication_ids, 2);
    OspreyFactorResult other_head = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
        OSPREY_POTENTIAL_IMPLICATION, 0, false, 0.8, implication_ids, 2);
    OspreyFactorResult other_stage = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_SECONDARY,
        OSPREY_POTENTIAL_IMPLICATION, 1, false, 0.8, implication_ids, 2);
    OspreyFactorResult other_polarity = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
        OSPREY_POTENTIAL_IMPLICATION, 1, true, 0.8, implication_ids, 2);
    OspreyFactorResult other_probability = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
        OSPREY_POTENTIAL_IMPLICATION, 1, false, 0.5, implication_ids, 2);
    CHECK(ordered.inserted && other_head.inserted && other_stage.inserted &&
          other_polarity.inserted && other_probability.inserted &&
          reverse.id != ordered.id,
          "factor identity retains order, head, stage, polarity, and p bits");

    uint32_t bad_ids[2] = { 0, 0 };
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                               OSPREY_POTENTIAL_IMPLICATION, 1, false, 0.8,
                               bad_ids, 2).status == OSPREY_INVALID_GRAPH,
          "duplicate semantic roles rejected");
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                               OSPREY_POTENTIAL_PRIOR, 1, false, 0.8,
                               one, 1).status == OSPREY_INVALID_GRAPH,
          "invalid prior head rejected");
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                               OSPREY_POTENTIAL_IMPLICATION, 1, false, NAN,
                               implication_ids, 2).status == OSPREY_INVALID_GRAPH,
          "NaN probability rejected");
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                               OSPREY_POTENTIAL_IMPLICATION, 1, false, 1.1,
                               implication_ids, 2).status == OSPREY_INVALID_GRAPH,
          "out-of-range probability rejected");
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_COUNT, OSPREY_GRAPH_BASE_CA,
                               OSPREY_POTENTIAL_PRIOR, 0, false, 0.8,
                               one, 1).status == OSPREY_INVALID_GRAPH,
          "nonexistent rule rejected");
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                               OSPREY_POTENTIAL_IMPLICATION, 0, false, 0.8,
                               implication_ids, 5).status == OSPREY_INVALID_GRAPH,
          "oversized arity rejected without truncation");
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                               OSPREY_POTENTIAL_PRIOR, 0, false, 0.8,
                               one, 0).status == OSPREY_INVALID_GRAPH,
          "zero arity rejected");
    uint32_t bad_id[1] = { UINT32_MAX };
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                               OSPREY_POTENTIAL_PRIOR, 0, false, 0.8,
                               bad_id, 1).status == OSPREY_INVALID_GRAPH,
          "out-of-range variable ID rejected");
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                               OSPREY_POTENTIAL_PRIOR, 0, false, INFINITY,
                               one, 1).status == OSPREY_INVALID_GRAPH,
          "infinite probability rejected");
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CA01, 0,
                               OSPREY_POTENTIAL_PRIOR, 0, false, 0.8,
                               one, 1).status == OSPREY_INVALID_GRAPH,
          "unknown graph stage rejected");
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CA01,
                               OSPREY_GRAPH_BASE_CA, 0, 0, false, 0.8,
                               one, 1).status == OSPREY_INVALID_GRAPH,
          "unknown potential kind rejected");
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CB06,
                               OSPREY_GRAPH_SECONDARY,
                               OSPREY_POTENTIAL_HARD_FALSE, UINT16_MAX,
                               false, 0.8, one, 1).status == OSPREY_INVALID_GRAPH,
          "hard false rejects probability metadata");
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CB06,
                               OSPREY_GRAPH_SECONDARY,
                               OSPREY_POTENTIAL_HARD_FALSE, UINT16_MAX,
                               true, 0.0, one, 1).status == OSPREY_INVALID_GRAPH,
          "hard false rejects polarity metadata");
    osprey_free(ctx);

    config.max_factors = 1;
    ctx = new_graph_context(&config);
    CHECK(add_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &chunks[0]).inserted,
          "factor cap variable");
    OspreyFactorResult first = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
        OSPREY_POTENTIAL_PRIOR, 0, false, 0.8, one, 1);
    OspreyFactorResult same = osprey_factor_add_ex(
        ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
        OSPREY_POTENTIAL_PRIOR, 0, false, 0.8, one, 1);
    CHECK(first.status == OSPREY_OK && same.status == OSPREY_OK &&
          !same.inserted, "duplicate factor accepted at full factor cap");
    CHECK(osprey_factor_add_ex(ctx, OSPREY_RULE_CA08, OSPREY_GRAPH_BASE_CA,
                               OSPREY_POTENTIAL_PRIOR, 0, false, 0.8,
                               one, 1).status == OSPREY_LIMIT_EXCEEDED,
          "new factor at full cap rejects");
    osprey_free(ctx);
}

static void test_factor_compiler_helpers(void)
{
    OspreyConfig config = graph_config();
    OspreyContext *ctx = new_graph_context(&config);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk chunks[4];
    for (unsigned i = 0; i < G_N_ELEMENTS(chunks); i++) {
        chunks[i] = make_chunk(region, (int64_t)i * 8, 8);
        CHECK(add_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &chunks[i]).inserted,
              "factor helper variable inserted");
    }

    OspreyFactorBatchResult batch = osprey_factor_add_bidirectional(
        ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA, false, 0.8, 0, 1);
    CHECK(batch.status == OSPREY_OK && batch.inserted == 2,
          "bidirectional helper inserts both directions");
    OspreyFactor *forward = g_array_index(ctx->graph->factors,
                                          OspreyFactor *, 0);
    OspreyFactor *reverse = g_array_index(ctx->graph->factors,
                                          OspreyFactor *, 1);
    CHECK(forward->head_idx == 1 && forward->var_ids[0] == 0 &&
          forward->var_ids[1] == 1 && reverse->head_idx == 1 &&
          reverse->var_ids[0] == 1 && reverse->var_ids[1] == 0,
          "bidirectional helper preserves semantic roles");
    batch = osprey_factor_add_bidirectional(
        ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA, false, 0.8, 0, 1);
    CHECK(batch.status == OSPREY_OK && batch.inserted == 0,
          "bidirectional helper reports exact duplicate count");

    uint32_t antecedents[2] = { 0, 1 };
    batch = osprey_factor_add_conjunction_bidirectional(
        ctx, OSPREY_RULE_CD08, OSPREY_GRAPH_SECONDARY, false, 0.8,
        antecedents, G_N_ELEMENTS(antecedents), 2);
    CHECK(batch.status == OSPREY_OK && batch.inserted == 3,
          "conjunction bidirectional helper splits reverse heads");
    OspreyFactor *to_head = g_array_index(ctx->graph->factors,
                                          OspreyFactor *, 2);
    CHECK(to_head->num_vars == 3 && to_head->head_idx == 2 &&
          to_head->var_ids[0] == 0 && to_head->var_ids[1] == 1 &&
          to_head->var_ids[2] == 2,
          "conjunction helper keeps printed antecedent order");

    uint32_t heads[2] = { 2, 3 };
    batch = osprey_factor_add_multi_head(
        ctx, OSPREY_RULE_CB01, OSPREY_GRAPH_SECONDARY, false, 0.8,
        NULL, 0, heads, G_N_ELEMENTS(heads));
    CHECK(batch.status == OSPREY_OK && batch.inserted == 2,
          "deterministic multi-head helper emits unary priors");
    uint32_t antecedent = 0;
    batch = osprey_factor_add_multi_head(
        ctx, OSPREY_RULE_CB01, OSPREY_GRAPH_SECONDARY, false, 0.8,
        &antecedent, 1, heads, G_N_ELEMENTS(heads));
    CHECK(batch.status == OSPREY_OK && batch.inserted == 2,
          "probabilistic multi-head helper emits implications");

    OspreyFactorResult hard = osprey_factor_add_hard_false(
        ctx, OSPREY_RULE_CB06, OSPREY_GRAPH_SECONDARY, 3);
    CHECK(hard.status == OSPREY_OK && hard.inserted,
          "hard-false helper emits exact hard potential");
    CHECK(osprey_factor_add_implication(
              ctx, OSPREY_RULE_CA04, OSPREY_GRAPH_BASE_CA, false, 0.8,
              NULL, 0, 1).status == OSPREY_INVALID_GRAPH,
          "implication helper rejects an empty antecedent list");
    CHECK(osprey_factor_add_multi_head(
              ctx, OSPREY_RULE_CB01, OSPREY_GRAPH_SECONDARY, false, 0.8,
              NULL, 0, NULL, 0).status == OSPREY_INVALID_GRAPH,
          "multi-head helper rejects an empty head list");
    osprey_free(ctx);
}

static char *dump_context(bool reverse)
{
    OspreyConfig config = graph_config();
    OspreyContext *ctx = new_graph_context(&config);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk chunks[3] = {
        make_chunk(region, -8, 8),
        make_chunk(region, 0, 8),
        make_chunk(region, 8, 8),
    };
    uint32_t ids[3];
    for (unsigned n = 0; n < 3; n++) {
        unsigned index = reverse ? 2 - n : n;
        OspreyInternResult result = add_var(
            ctx, OSPREY_PRED_PRIMITIVE_VAR, &chunks[index]);
        ids[index] = result.id;
    }
    uint32_t first[2] = { ids[0], ids[1] };
    uint32_t second[2] = { ids[1], ids[2] };
    if (reverse) {
        osprey_factor_add_ex(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                             OSPREY_POTENTIAL_IMPLICATION, 1, false, 0.8,
                             second, 2);
        osprey_factor_add_ex(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                             OSPREY_POTENTIAL_IMPLICATION, 1, false, 0.8,
                             first, 2);
    } else {
        osprey_factor_add_ex(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                             OSPREY_POTENTIAL_IMPLICATION, 1, false, 0.8,
                             first, 2);
        osprey_factor_add_ex(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                             OSPREY_POTENTIAL_IMPLICATION, 1, false, 0.8,
                             second, 2);
    }
    FILE *tmp = tmpfile();
    CHECK(tmp != NULL, "temporary graph dump");
    CHECK(osprey_graph_dump_file(ctx, tmp), "graph dump file succeeds");
    fflush(tmp);
    fseek(tmp, 0, SEEK_END);
    long length = ftell(tmp);
    CHECK(length >= 0, "graph dump length");
    rewind(tmp);
    char *text = g_malloc((size_t)length + 1);
    size_t read_count = fread(text, 1, (size_t)length, tmp);
    text[read_count] = '\0';
    fclose(tmp);
    osprey_free(ctx);
    return text;
}

static void test_canonical_dump_permutation(void)
{
    char *forward = dump_context(false);
    char *reverse = dump_context(true);
    CHECK(strcmp(forward, reverse) == 0,
          "canonical graph dump ignores insertion and runtime IDs");
    CHECK(strstr(forward, "PREDICATES 3") != NULL &&
          strstr(forward, "FACTORS 2") != NULL,
          "canonical graph dump contains sorted graph sections");
    const char *negative = strstr(forward, ":fffffffffffffff8:8}");
    const char *zero = strstr(forward, ":0000000000000000:8}");
    CHECK(negative != NULL && zero != NULL && negative < zero,
          "canonical predicate dump sorts signed offsets");
    g_free(forward);
    g_free(reverse);
}

int main(void)
{
    RUN(test_predicate_identity);
    RUN(test_candidate_selection_and_caps);
    RUN(test_candidate_permutations);
    RUN(test_candidate_extent_validation);
    RUN(test_factor_potentials_and_validation);
    RUN(test_factor_compiler_helpers);
    RUN(test_canonical_dump_permutation);
    CHECK(registered == executed, "every registered graph case executed");
    if (failures != 0 || registered != executed) {
        fprintf(stderr, "FAIL stage3_graph (%u failures, %u/%u)\n",
                failures, executed, registered);
        return 1;
    }
    printf("PASS stage3_graph (%u/%u)\n", executed, registered);
    return 0;
}
