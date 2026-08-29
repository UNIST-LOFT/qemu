#include "osprey.h"
#include "osprey-internal.h"
#include "stage5_bp_reference.h"

#include <float.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned failures;
static unsigned registered;
static unsigned executed;

#define CHECK(condition, message) do {                                      \
    if (!(condition)) {                                                      \
        fprintf(stderr, "FAIL: %s (line %d)\n", (message), __LINE__);      \
        failures++;                                                          \
    }                                                                            \
} while (0)

#define RUN(test) do {                                                       \
    registered++;                                                            \
    test();                                                                  \
    executed++;                                                              \
} while (0)

static OspreyConfig bp_config(void)
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

static OspreyChunk make_chunk(OspreyRegionId region, int64_t offset,
                              uint64_t size)
{
    OspreyChunk chunk;
    memset(&chunk, 0, sizeof(chunk));
    chunk.address.region = region;
    chunk.address.offset = offset;
    chunk.size = size;
    return chunk;
}

static OspreyContext *new_context_with_config(const OspreyConfig *config)
{
    OspreyContext *ctx = osprey_new(config);
    if (ctx != NULL) ctx->graph = osprey_graph_new();
    return ctx;
}

static OspreyContext *new_context(void)
{
    OspreyConfig config = bp_config();
    return new_context_with_config(&config);
}

static uint32_t add_primitive(OspreyContext *ctx, OspreyRegionId region,
                              int64_t offset)
{
    OspreyVarPayload payload;
    OspreyInternResult result;
    memset(&payload, 0, sizeof(payload));
    payload.chunk = make_chunk(region, offset, 8);
    result = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &payload);
    CHECK(result.id != UINT32_MAX, "primitive variable inserted");
    return result.id;
}

static bool add_prior(OspreyContext *ctx, uint32_t id, double probability)
{
    OspreyFactorResult result = osprey_factor_add_prior(
        ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, false, probability, id);
    CHECK(result.status == OSPREY_OK, "base prior inserted");
    return result.status == OSPREY_OK;
}

static bool add_secondary(OspreyContext *ctx, uint16_t rule,
                          const uint32_t *ids, uint32_t antecedents,
                          uint32_t head)
{
    OspreyFactorResult result = osprey_factor_add_implication(
        ctx, rule, OSPREY_GRAPH_SECONDARY, false, 0.8, ids, antecedents,
        head);
    CHECK(result.status == OSPREY_OK, "secondary implication inserted");
    return result.status == OSPREY_OK;
}

static void set_seed(OspreyContext *ctx, uint32_t id, double belief)
{
    OspreyVar *variable = &g_array_index(ctx->graph->vars, OspreyVar, id);
    variable->belief = belief;
    variable->belief_valid = 1;
}

static uint32_t local_for_offset(const OspreyContext *ctx,
                                 const OspreyBpGraph *graph, int64_t offset)
{
    for (guint local = 0; local < graph->vars->len; local++) {
        const OspreyBpVarRef *ref = &g_array_index(graph->vars,
                                                   OspreyBpVarRef, local);
        const OspreyVar *variable = &g_array_index(
            ctx->graph->vars, OspreyVar, ref->graph_var_id);
        if (variable->kind == OSPREY_PRED_PRIMITIVE_VAR &&
            variable->payload.chunk.address.offset == offset) return local;
    }
    return UINT32_MAX;
}

static char *dump_graph(const OspreyContext *ctx, const OspreyBpGraph *graph)
{
    char *data = NULL;
    size_t length = 0;
    FILE *out = open_memstream(&data, &length);
    if (out == NULL) return NULL;
    if (!osprey_bp_graph_dump_file(ctx, graph, out) || fclose(out) != 0) {
        free(data);
        return NULL;
    }
    return data;
}

static void test_bp_configuration(void)
{
    const char *name = "BINRADAR_OSPREY_MAX_BP_TABLE_MB";
    char *saved = g_strdup(g_getenv(name));
    OspreyConfig config;

    g_unsetenv(name);
    CHECK(osprey_config_from_env(&config) &&
              config.max_bp_table_bytes == 256u * 1024u * 1024u,
          "BP workspace configuration uses the default budget");
    g_setenv(name, "1", TRUE);
    CHECK(osprey_config_from_env(&config) &&
          config.max_bp_table_bytes == 1024u * 1024u,
          "BP workspace configuration parses exact MiB");
    g_setenv(name, "1MiB", TRUE);
    CHECK(!osprey_config_from_env(&config),
          "BP workspace configuration rejects suffixes");
    g_setenv(name, "0", TRUE);
    CHECK(!osprey_config_from_env(&config),
          "BP workspace configuration rejects zero");
    g_setenv(name, "1 ", TRUE);
    CHECK(!osprey_config_from_env(&config),
          "BP workspace configuration rejects trailing data");
    g_setenv(name, "+1", TRUE);
    CHECK(!osprey_config_from_env(&config),
          "BP workspace configuration rejects non-decimal prefixes");
    g_setenv(name, "18446744073709551616", TRUE);
    CHECK(!osprey_config_from_env(&config),
          "BP workspace configuration rejects integer overflow");
    g_setenv(name, "4097", TRUE);
    CHECK(!osprey_config_from_env(&config),
          "BP workspace configuration rejects values above the bound");
    if (saved != NULL) {
        g_setenv(name, saved, TRUE);
    } else {
        g_unsetenv(name);
    }
    g_free(saved);
}

static void test_basic_projection(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t a = add_primitive(ctx, region, 0);
    uint32_t b = add_primitive(ctx, region, 8);
    uint32_t c = add_primitive(ctx, region, 16);
    uint32_t ids[1] = { a };
    OspreyBpGraph *graph = NULL;

    set_seed(ctx, a, 0.0);
    set_seed(ctx, b, 1.0);
    add_prior(ctx, a, 0.0);
    add_prior(ctx, b, 1.0);
    add_secondary(ctx, OSPREY_RULE_CB02, ids, 1, c);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "basic complete projection builds");
    CHECK(graph != NULL && osprey_bp_graph_validate(ctx, graph),
          "basic projection validates in both directions");
    CHECK(graph != NULL && stage5_bp_reference_matches(ctx, graph),
          "basic projection matches independent ownership oracle");
    if (graph != NULL) {
        uint32_t local_a = local_for_offset(ctx, graph, 0);
        uint32_t local_b = local_for_offset(ctx, graph, 8);
        uint32_t local_c = local_for_offset(ctx, graph, 16);
        CHECK(local_a != UINT32_MAX && local_b != UINT32_MAX &&
                  local_c != UINT32_MAX,
              "all basic variables have canonical local IDs");
        CHECK(graph->components->len == 2,
              "secondary bridge creates the expected complete components");
        for (guint i = 0; i < graph->edges->len; i++) {
            const OspreyBpEdge *edge = &g_array_index(graph->edges,
                                                      OspreyBpEdge, i);
            const OspreyBpVarRef *ref = &g_array_index(
                graph->vars, OspreyBpVarRef, edge->local_var);
            const double *message = &graph->msg_vf_current[(size_t)i * 2u];
            if (edge->local_var == local_a) {
                CHECK(ref->base_seed_valid && message[0] == 0.0 &&
                          message[1] == -INFINITY,
                      "exact zero seed is not epsilon-clamped");
            } else if (edge->local_var == local_b) {
                CHECK(ref->base_seed_valid && message[0] == -INFINITY &&
                          message[1] == 0.0,
                      "exact one seed is not epsilon-clamped");
            } else if (edge->local_var == local_c) {
                CHECK(!ref->base_seed_valid &&
                          message[0] == -log(2.0) &&
                          message[1] == -log(2.0),
                      "secondary-only variable starts uniformly");
            }
        }
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_arity_and_components(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x10);
    uint32_t ids[8];
    uint32_t three[2];
    uint32_t four[3];
    OspreyBpGraph *graph = NULL;

    for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) {
        ids[i] = add_primitive(ctx, region, (int64_t)i * 8);
        add_prior(ctx, ids[i], 0.5);
    }
    three[0] = ids[0];
    three[1] = ids[1];
    four[0] = ids[3];
    four[1] = ids[4];
    four[2] = ids[5];
    add_secondary(ctx, OSPREY_RULE_CB02, three, 2, ids[2]);
    add_secondary(ctx, OSPREY_RULE_CB03, four, 3, ids[6]);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK &&
              osprey_bp_graph_validate(ctx, graph) &&
              stage5_bp_reference_matches(ctx, graph),
          "arity-three/four projection matches the independent oracle");
    CHECK(graph != NULL && graph->components->len == 3,
          "disconnected complete graph components are retained");
    if (graph != NULL) {
        bool saw_three = false, saw_four = false;
        for (guint i = 0; i < graph->factors->len; i++) {
            const OspreyBpFactorRef *ref = &g_array_index(
                graph->factors, OspreyBpFactorRef, i);
            if (ref->factor_edge_count == 3) saw_three = true;
            if (ref->factor_edge_count == 4) saw_four = true;
        }
        CHECK(saw_three && saw_four,
              "factor CSR preserves arity-three and arity-four roles");
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_cross_region_bridge(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyRegionId stack = make_region(OSPREY_REGION_STACK_FUNCTION, 0x100);
    uint32_t left = add_primitive(ctx, global, 0);
    uint32_t right = add_primitive(ctx, stack, -8);
    uint32_t antecedent = left;
    OspreyBpGraph *graph = NULL;

    add_prior(ctx, left, 0.25);
    add_prior(ctx, right, 0.75);
    add_secondary(ctx, OSPREY_RULE_CD01, &antecedent, 1, right);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK &&
              osprey_bp_graph_validate(ctx, graph) &&
              stage5_bp_reference_matches(ctx, graph),
          "cross-region secondary bridge builds canonically");
    CHECK(graph != NULL && graph->components->len == 1,
          "cross-region bridge is one BP component");
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_exact_seed_values(void)
{
    const double probabilities[] = {
        0.0, 1.0, DBL_MIN, 0.5, nextafter(1.0, 0.0)
    };
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x20);
    OspreyBpGraph *graph = NULL;

    for (unsigned i = 0; i < G_N_ELEMENTS(probabilities); i++) {
        uint32_t id = add_primitive(ctx, region, (int64_t)i * 8);
        set_seed(ctx, id, probabilities[i]);
        add_prior(ctx, id, probabilities[i]);
    }
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK &&
              osprey_bp_graph_validate(ctx, graph),
          "all exact seed values build without clamping");
    if (graph != NULL) {
        for (unsigned i = 0; i < G_N_ELEMENTS(probabilities); i++) {
            uint32_t local = local_for_offset(ctx, graph, (int64_t)i * 8);
            CHECK(local != UINT32_MAX,
                  "exact seed has a canonical local variable");
            if (local == UINT32_MAX) continue;
            const OspreyBpVarRef *ref = &g_array_index(
                graph->vars, OspreyBpVarRef, local);
            CHECK(ref->base_seed_valid &&
                      ref->base_seed[1] == probabilities[i],
                  "base seed retains exact probability payload");
            for (guint edge_id = 0; edge_id < graph->edges->len; edge_id++) {
                const OspreyBpEdge *edge = &g_array_index(
                    graph->edges, OspreyBpEdge, edge_id);
                if (edge->local_var != local) continue;
                double expected_zero = probabilities[i] == 1.0
                    ? 0.0 : 1.0 - probabilities[i];
                double expected_one = probabilities[i];
                double expected_log_zero = expected_zero == 0.0
                    ? -INFINITY : log(expected_zero);
                double expected_log_one = expected_one == 0.0
                    ? -INFINITY : log(expected_one);
                const double *message = &graph->msg_vf_current[
                    (size_t)edge_id * 2u];
                CHECK(message[0] == expected_log_zero &&
                          message[1] == expected_log_one,
                      "seed message uses exact log-domain endpoints");
            }
        }
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_secondary_uniform_seed(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x30);
    uint32_t first = add_primitive(ctx, region, 0);
    uint32_t second = add_primitive(ctx, region, 8);
    OspreyBpGraph *graph = NULL;

    add_secondary(ctx, OSPREY_RULE_CB02, &first, 1, second);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK &&
              osprey_bp_graph_validate(ctx, graph),
          "secondary-only graph builds");
    if (graph != NULL) {
        for (guint i = 0; i < graph->vars->len; i++) {
            const OspreyBpVarRef *ref = &g_array_index(graph->vars,
                                                       OspreyBpVarRef, i);
            CHECK(!ref->base_seed_valid,
                  "secondary-only variable has invalid base seed");
        }
        for (guint i = 0; i < graph->edges->len; i++) {
            CHECK(graph->msg_vf_current[(size_t)i * 2u] == -log(2.0) &&
                      graph->msg_vf_current[(size_t)i * 2u + 1u] == -log(2.0),
                  "secondary-only messages are normalized uniform seeds");
        }
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static OspreyContext *permutation_context(bool reverse)
{
    OspreyConfig config = bp_config();
    OspreyContext *ctx = new_context_with_config(&config);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x40);
    uint32_t ids[4];
    uint32_t order[4] = { 0, 1, 2, 3 };

    if (reverse) {
        for (unsigned i = 0; i < 4; i++) order[i] = 3 - i;
    }
    for (unsigned i = 0; i < 4; i++) {
        ids[order[i]] = add_primitive(ctx, region, (int64_t)order[i] * 8);
    }
    for (unsigned i = 0; i < 4; i++) set_seed(ctx, ids[i], 0.2 + i * 0.1);
    if (!reverse) {
        for (unsigned i = 0; i < 4; i++) add_prior(ctx, ids[i], 0.2 + i * 0.1);
        uint32_t first[2] = { ids[0], ids[1] };
        uint32_t second[3] = { ids[0], ids[1], ids[2] };
        add_secondary(ctx, OSPREY_RULE_CB02, first, 2, ids[2]);
        add_secondary(ctx, OSPREY_RULE_CB03, second, 3, ids[3]);
    } else {
        uint32_t first[2] = { ids[0], ids[1] };
        uint32_t second[3] = { ids[0], ids[1], ids[2] };
        add_secondary(ctx, OSPREY_RULE_CB03, second, 3, ids[3]);
        add_secondary(ctx, OSPREY_RULE_CB02, first, 2, ids[2]);
        for (int i = 3; i >= 0; i--) {
            add_prior(ctx, ids[i], 0.2 + i * 0.1);
        }
    }
    return ctx;
}

static void test_permutation_dump(void)
{
    OspreyContext *left = permutation_context(false);
    OspreyContext *right = permutation_context(true);
    OspreyBpGraph *left_graph = NULL;
    OspreyBpGraph *right_graph = NULL;
    char *left_dump = NULL;
    char *right_dump = NULL;

    CHECK(osprey_bp_graph_build(left, &left_graph) == OSPREY_OK &&
              osprey_bp_graph_build(right, &right_graph) == OSPREY_OK,
          "permuted graphs build");
    if (left_graph != NULL && right_graph != NULL) {
        left_dump = dump_graph(left, left_graph);
        right_dump = dump_graph(right, right_graph);
        CHECK(left_dump != NULL && right_dump != NULL &&
                  strcmp(left_dump, right_dump) == 0,
              "canonical projection and seed dumps ignore insertion IDs");
    }
    free(left_dump);
    free(right_dump);
    osprey_bp_graph_free(left_graph);
    osprey_bp_graph_free(right_graph);
    osprey_free(left);
    osprey_free(right);
}

static void expect_invalid(OspreyContext *ctx, const char *message)
{
    OspreyBpGraph *graph = NULL;
    OspreyStatus status = osprey_bp_graph_build(ctx, &graph);
    CHECK(status == OSPREY_INVALID_GRAPH && graph == NULL, message);
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_malformed_inputs(void)
{
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x50);
    OspreyContext *ctx;
    OspreyFactor *factor;
    uint32_t ids[2];

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    g_array_index(ctx->graph->vars, OspreyVar, ids[0]).id = 99;
    expect_invalid(ctx, "mismatched variable ID rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    OspreyVar duplicate = g_array_index(ctx->graph->vars, OspreyVar, ids[0]);
    duplicate.id = 1;
    g_array_append_val(ctx->graph->vars, duplicate);
    add_prior(ctx, ids[0], 0.5);
    expect_invalid(ctx, "duplicate semantic variable rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    OspreyFactor *original = g_array_index(ctx->graph->factors,
                                           OspreyFactor *, 0);
    OspreyFactor *duplicate_factor = g_new(OspreyFactor, 1);
    *duplicate_factor = *original;
    duplicate_factor->id = 1;
    duplicate_factor->var_ids = g_new(uint32_t, original->num_vars);
    memcpy(duplicate_factor->var_ids, original->var_ids,
           (size_t)original->num_vars * sizeof(uint32_t));
    g_array_append_val(ctx->graph->factors, duplicate_factor);
    expect_invalid(ctx, "duplicate semantic factor rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 0);
    factor->id = 99;
    expect_invalid(ctx, "mismatched factor ID rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 0);
    factor->num_vars = OSPREY_FACTOR_MAX_ARITY + 1;
    expect_invalid(ctx, "factor arity above the bound rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 0);
    factor->p = INFINITY;
    expect_invalid(ctx, "positive-infinite factor probability rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    ids[1] = add_primitive(ctx, region, 8);
    add_prior(ctx, ids[0], 0.5);
    add_prior(ctx, ids[1], 0.5);
    uint32_t antecedent = ids[0];
    add_secondary(ctx, OSPREY_RULE_CB02, &antecedent, 1, ids[1]);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 2);
    factor->var_ids[1] = factor->var_ids[0];
    expect_invalid(ctx, "repeated factor role rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 0);
    factor->stage = OSPREY_GRAPH_SECONDARY;
    expect_invalid(ctx, "bad stage and rule pairing rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 0);
    factor->p = NAN;
    expect_invalid(ctx, "non-finite factor probability rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    ids[1] = add_primitive(ctx, region, 8);
    add_prior(ctx, ids[0], 0.5);
    add_prior(ctx, ids[1], 0.5);
    antecedent = ids[0];
    add_secondary(ctx, OSPREY_RULE_CB02, &antecedent, 1, ids[1]);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 2);
    factor->head_idx = 2;
    expect_invalid(ctx, "bad factor head rejects");

    ctx = new_context();
    add_primitive(ctx, region, 0);
    expect_invalid(ctx, "factorless variable rejects");
}

static void test_reverse_adjacency_validation(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x60);
    uint32_t first = add_primitive(ctx, region, 0);
    uint32_t second = add_primitive(ctx, region, 8);
    uint32_t antecedent = first;
    OspreyBpGraph *graph = NULL;

    add_prior(ctx, first, 0.5);
    add_prior(ctx, second, 0.5);
    add_secondary(ctx, OSPREY_RULE_CB02, &antecedent, 1, second);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK,
          "reverse-adjacency fixture builds");
    if (graph != NULL && graph->var_edges->len > 1) {
        uint32_t saved = g_array_index(graph->var_edges, uint32_t, 0);
        g_array_index(graph->var_edges, uint32_t, 0) =
            g_array_index(graph->var_edges, uint32_t, 1);
        CHECK(!osprey_bp_graph_validate(ctx, graph),
              "overwritten variable adjacency is rejected");
        g_array_index(graph->var_edges, uint32_t, 0) = saved;
        OspreyBpEdge *edge = &g_array_index(graph->edges, OspreyBpEdge, 0);
        uint32_t saved_position = edge->key.factor_position;
        edge->key.factor_position = saved_position + 1;
        CHECK(!osprey_bp_graph_validate(ctx, graph),
              "corrupted semantic edge role is rejected");
        edge->key.factor_position = saved_position;
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_component_maximality_validation(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x70);
    uint32_t first_id = add_primitive(ctx, region, 0);
    uint32_t second_id = add_primitive(ctx, region, 8);
    OspreyBpGraph *graph = NULL;

    add_prior(ctx, first_id, 0.5);
    add_prior(ctx, second_id, 0.5);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK &&
              graph != NULL && graph->components->len == 2,
          "disconnected-component validation fixture builds");
    if (graph != NULL && graph->components->len == 2) {
        OspreyBpComponent *first = g_ptr_array_index(graph->components, 0);
        OspreyBpComponent *second = g_ptr_array_index(graph->components, 1);
        uint64_t removed_bytes = sizeof(*second) + 3u * sizeof(GArray) +
                                 sizeof(gpointer);

        g_array_append_vals(first->local_vars, second->local_vars->data,
                            second->local_vars->len);
        g_array_append_vals(first->local_factors, second->local_factors->data,
                            second->local_factors->len);
        g_array_append_vals(first->edges, second->edges->data,
                            second->edges->len);
        g_ptr_array_remove_index(graph->components, 1);
        g_array_free(second->local_vars, TRUE);
        g_array_free(second->local_factors, TRUE);
        g_array_free(second->edges, TRUE);
        g_free(second);
        graph->workspace_bytes -= removed_bytes;

        CHECK(!osprey_bp_graph_validate(ctx, graph),
              "validator rejects one component containing disconnected subgraphs");
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static OspreyStatus build_basic_with_limit(uint64_t limit,
                                           OspreyBpGraph **out)
{
    OspreyConfig config = bp_config();
    OspreyContext *ctx;
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x80);
    uint32_t ids[3];
    OspreyStatus status;

    config.max_bp_table_bytes = limit;
    ctx = new_context_with_config(&config);
    ids[0] = add_primitive(ctx, region, 0);
    ids[1] = add_primitive(ctx, region, 8);
    ids[2] = add_primitive(ctx, region, 16);
    add_prior(ctx, ids[0], 0.25);
    add_prior(ctx, ids[1], 0.5);
    add_prior(ctx, ids[2], 0.75);
    uint32_t antecedents[2] = { ids[0], ids[1] };
    add_secondary(ctx, OSPREY_RULE_CB02, antecedents, 2, ids[2]);
    status = osprey_bp_graph_build(ctx, out);
    if (status != OSPREY_OK) osprey_bp_graph_free(*out);
    osprey_free(ctx);
    return status;
}

static void test_workspace_boundaries(void)
{
    OspreyConfig config = bp_config();
    OspreyContext *probe_ctx = new_context_with_config(&config);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x80);
    uint32_t ids[3];
    OspreyBpGraph *probe = NULL;
    uint64_t required;

    ids[0] = add_primitive(probe_ctx, region, 0);
    ids[1] = add_primitive(probe_ctx, region, 8);
    ids[2] = add_primitive(probe_ctx, region, 16);
    add_prior(probe_ctx, ids[0], 0.25);
    add_prior(probe_ctx, ids[1], 0.5);
    add_prior(probe_ctx, ids[2], 0.75);
    uint32_t antecedents[2] = { ids[0], ids[1] };
    add_secondary(probe_ctx, OSPREY_RULE_CB02, antecedents, 2, ids[2]);
    CHECK(osprey_bp_graph_build(probe_ctx, &probe) == OSPREY_OK &&
              probe != NULL && osprey_bp_graph_validate(probe_ctx, probe),
          "workspace probe builds");
    required = probe == NULL ? 0 : probe->workspace_bytes;
    osprey_bp_graph_free(probe);
    osprey_free(probe_ctx);
    if (required != 0) {
        OspreyBpGraph *at_bound = NULL;
        OspreyBpGraph *below_bound = NULL;
        CHECK(build_basic_with_limit(required, &at_bound) == OSPREY_OK &&
                  at_bound != NULL,
              "workspace succeeds exactly at its checked bound");
        CHECK(build_basic_with_limit(required - 1, &below_bound) ==
                  OSPREY_LIMIT_EXCEEDED && below_bound == NULL,
              "workspace rejects one byte below its checked bound");
        osprey_bp_graph_free(at_bound);
        osprey_bp_graph_free(below_bound);
    }
}

static void test_allocation_failures(void)
{
    bool saw_success = false;
    int64_t success_at = -1;

    for (int64_t fail_after = 0; fail_after < 256; fail_after++) {
        OspreyContext *ctx = new_context();
        OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x90);
        uint32_t first = add_primitive(ctx, region, 0);
        uint32_t second = add_primitive(ctx, region, 8);
        uint32_t antecedent = first;
        OspreyBpGraph *graph = NULL;
        add_prior(ctx, first, 0.5);
        add_prior(ctx, second, 0.5);
        add_secondary(ctx, OSPREY_RULE_CB02, &antecedent, 1, second);
        osprey_bp_test_set_alloc_fail_after(fail_after);
        OspreyStatus status = osprey_bp_graph_build(ctx, &graph);
        osprey_bp_test_set_alloc_fail_after(-1);
        if (status == OSPREY_OK) {
            saw_success = true;
            success_at = fail_after;
            CHECK(graph != NULL && osprey_bp_graph_validate(ctx, graph),
                  "allocation-failure sweep eventually builds a valid graph");
        } else {
            CHECK(status == OSPREY_INVALID_GRAPH && graph == NULL,
                  "allocation failure rejects without a partial graph");
        }
        osprey_bp_graph_free(graph);
        osprey_free(ctx);
        if (saw_success) break;
    }
    CHECK(saw_success && success_at > 0,
          "every owned BP allocation has a deterministic failure point");
}

static void test_rebuild_after_failure(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0xa0);
    uint32_t id = add_primitive(ctx, region, 0);
    OspreyBpGraph *graph = NULL;

    add_prior(ctx, id, 0.5);
    osprey_bp_test_set_alloc_fail_after(0);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_INVALID_GRAPH &&
              graph == NULL, "first BP allocation failure is isolated");
    osprey_bp_test_set_alloc_fail_after(-1);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL &&
              osprey_bp_graph_validate(ctx, graph),
          "build after failure succeeds");
    osprey_bp_graph_free(graph);
    graph = NULL;
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL &&
              osprey_bp_graph_validate(ctx, graph),
          "repeated build and free remain deterministic");
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static uint32_t next_random(uint32_t *state)
{
    *state = *state * 1664525u + 1013904223u;
    return *state;
}

static void test_generated_projections(void)
{
    uint32_t state = 0x5eeda11u;
    unsigned generated = 0;

    for (unsigned sample = 0; sample < 2000; sample++) {
        OspreyContext *ctx = new_context();
        OspreyRegionId region = make_region(
            (next_random(&state) & 1u) ? OSPREY_REGION_GLOBAL
                                       : OSPREY_REGION_STACK_FUNCTION,
            0x100 + sample);
        uint32_t count = 1 + next_random(&state) % 8;
        uint32_t ids[8];
        uint32_t order[8];
        OspreyBpGraph *graph = NULL;
        bool ok = true;

        for (uint32_t i = 0; i < count; i++) order[i] = i;
        for (uint32_t i = count; i > 1; i--) {
            uint32_t selected = next_random(&state) % i;
            uint32_t swap = order[i - 1];
            order[i - 1] = order[selected];
            order[selected] = swap;
        }
        for (uint32_t position = 0; position < count; position++) {
            uint32_t i = order[position];
            ids[i] = add_primitive(ctx, region,
                                   (int64_t)i * 8 - (int64_t)(sample & 3u) * 8);
            set_seed(ctx, ids[i], (double)(next_random(&state) % 1001) / 1000.0);
            ok = add_prior(ctx, ids[i],
                           g_array_index(ctx->graph->vars, OspreyVar,
                                         ids[i]).belief) && ok;
        }
        if (count >= 3) {
            uint32_t antecedents[2] = { ids[0], ids[1] };
            ok = add_secondary(ctx, OSPREY_RULE_CB02, antecedents, 2,
                               ids[2]) && ok;
        }
        if (count >= 4) {
            uint32_t antecedents[3] = { ids[0], ids[1], ids[2] };
            ok = add_secondary(ctx, OSPREY_RULE_CB03, antecedents, 3,
                               ids[3]) && ok;
        }
        OspreyStatus status = osprey_bp_graph_build(ctx, &graph);
        bool production_valid = graph != NULL &&
            osprey_bp_graph_validate(ctx, graph);
        bool reference_valid = graph != NULL &&
            stage5_bp_reference_matches(ctx, graph);
        if (status != OSPREY_OK || graph == NULL || !production_valid ||
            !reference_valid) {
            fprintf(stderr, "generated projection mismatch at seed %u "
                    "status %d vars %u factors %u components %u valid %d ref %d\n",
                    sample, status, ctx->graph->vars->len,
                    ctx->graph->factors->len,
                    graph == NULL ? 0 : graph->components->len,
                    production_valid ? 1 : 0, reference_valid ? 1 : 0);
            ok = false;
        }
        if (ok) generated++;
        osprey_bp_graph_free(graph);
        osprey_free(ctx);
    }
    CHECK(generated == 2000, "all 2000 generated projection cases execute");
}

int main(void)
{
    RUN(test_bp_configuration);
    RUN(test_basic_projection);
    RUN(test_arity_and_components);
    RUN(test_cross_region_bridge);
    RUN(test_exact_seed_values);
    RUN(test_secondary_uniform_seed);
    RUN(test_permutation_dump);
    RUN(test_malformed_inputs);
    RUN(test_reverse_adjacency_validation);
    RUN(test_component_maximality_validation);
    RUN(test_workspace_boundaries);
    RUN(test_allocation_failures);
    RUN(test_rebuild_after_failure);
    RUN(test_generated_projections);

    if (failures != 0 || executed != registered) {
        fprintf(stderr, "FAIL stage5_bp (%u failures, %u/%u)\n",
                failures, executed, registered);
        return 1;
    }
    printf("PASS stage5_bp (%u/%u; generated 2000/2000)\n",
           executed, registered);
    return 0;
}
