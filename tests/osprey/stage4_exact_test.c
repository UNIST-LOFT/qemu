/* Stage 4.1 projection, Stage 4.2 clique topology, and Stage 4.3
 * exact-inference tests. */

#include "osprey.h"
#include "osprey-internal.h"
#include "stage4_exact_reference.h"

#include <float.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned failures;
static unsigned registered;
static unsigned executed;
static unsigned generated_registered;
static unsigned generated_executed;

static char *topology_dump(const OspreyExactTopology *topology);

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

static OspreyContext *new_graph_context_with_config(const OspreyConfig *config)
{
    OspreyContext *ctx = osprey_new(config);
    ctx->graph = osprey_graph_new();
    return ctx;
}

static OspreyContext *new_graph_context(void)
{
    OspreyConfig config = graph_config();
    return new_graph_context_with_config(&config);
}

static uint32_t add_primitive(OspreyContext *ctx, OspreyRegionId region,
                              int64_t offset)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.chunk = make_chunk(region, offset, 8);
    OspreyInternResult result = osprey_intern_var(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, &payload);
    CHECK(result.id != UINT32_MAX, "primitive variable inserted");
    return result.id;
}

static uint32_t add_scalar(OspreyContext *ctx, OspreyRegionId region,
                           int64_t offset)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.chunk = make_chunk(region, offset, 8);
    OspreyInternResult result = osprey_intern_var(
        ctx, OSPREY_PRED_SCALAR, &payload);
    CHECK(result.id != UINT32_MAX, "scalar variable inserted");
    return result.id;
}

static uint32_t add_field(OspreyContext *ctx, OspreyRegionId region,
                          int64_t offset, OspreyAddress base)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.attached.chunk = make_chunk(region, offset, 8);
    payload.attached.base = base;
    OspreyInternResult result = osprey_intern_var(
        ctx, OSPREY_PRED_FIELD_OF, &payload);
    CHECK(result.id != UINT32_MAX, "field variable inserted");
    return result.id;
}

static uint32_t add_primitive_access(OspreyContext *ctx,
                                     OspreyRegionId region, int64_t offset,
                                     uint64_t pc)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.prim_access.chunk = make_chunk(region, offset, 8);
    payload.prim_access.insn_pc = pc;
    OspreyInternResult result = osprey_intern_var(
        ctx, OSPREY_PRED_PRIMITIVE_ACCESS, &payload);
    CHECK(result.id != UINT32_MAX, "primitive-access variable inserted");
    return result.id;
}

static bool add_prior_probability(OspreyContext *ctx, uint16_t rule,
                                  uint8_t stage, double probability,
                                  uint32_t id)
{
    OspreyFactorResult result = osprey_factor_add_prior(
        ctx, rule, stage, false, probability, id);
    CHECK(result.status == OSPREY_OK, "prior factor inserted");
    return result.status == OSPREY_OK;
}

static bool add_prior(OspreyContext *ctx, uint16_t rule, uint8_t stage,
                      uint32_t id)
{
    return add_prior_probability(ctx, rule, stage, 0.8, id);
}

static bool add_implication_probability(
    OspreyContext *ctx, uint16_t rule, uint8_t stage, bool negative,
    double probability, const uint32_t *antecedents, uint32_t count,
    uint32_t target)
{
    OspreyFactorResult result = osprey_factor_add_implication(
        ctx, rule, stage, negative, probability, antecedents, count, target);
    CHECK(result.status == OSPREY_OK, "implication factor inserted");
    return result.status == OSPREY_OK;
}

static bool add_implication(OspreyContext *ctx, uint16_t rule, uint8_t stage,
                            uint32_t source, uint32_t target)
{
    return add_implication_probability(ctx, rule, stage, false, 0.8,
                                       &source, 1, target);
}

static OspreyExactComponent *component_for_local(const OspreyExactBase *base,
                                                  uint32_t local_id)
{
    for (guint i = 0; i < base->components->len; i++) {
        OspreyExactComponent *component = g_ptr_array_index(base->components, i);
        for (guint j = 0; j < component->local_vars->len; j++) {
            if (g_array_index(component->local_vars, uint32_t, j) == local_id) {
                return component;
            }
        }
    }
    return NULL;
}

static char *projection_dump(const OspreyContext *ctx,
                             const OspreyExactBase *base)
{
    GString *text = g_string_new("");
    const OspreyGraph *graph = ctx->graph;

    g_string_append_printf(text, "VARS %u\n", base->graph_var_ids->len);
    for (guint i = 0; i < base->graph_var_ids->len; i++) {
        uint32_t graph_id = g_array_index(base->graph_var_ids, uint32_t, i);
        const OspreyVar *var = &g_array_index(graph->vars, OspreyVar, graph_id);
        OspreyKey key = osprey_var_key(var->kind, &var->payload);
        g_string_append_printf(text, "%u %u", i, (unsigned)var->kind);
        for (guint word = 0; word < G_N_ELEMENTS(key.w); word++) {
            g_string_append_printf(text, " %016llx",
                                   (unsigned long long)key.w[word]);
        }
        g_string_append_c(text, '\n');
    }

    g_string_append_printf(text, "FACTORS %u\n", base->factor_refs->len);
    for (guint i = 0; i < base->factor_refs->len; i++) {
        const OspreyExactFactorRef *ref = &g_array_index(
            base->factor_refs, OspreyExactFactorRef, i);
        const OspreyFactor *factor = g_array_index(
            graph->factors, OspreyFactor *, ref->graph_factor_id);
        uint64_t p_bits;
        memcpy(&p_bits, &factor->p, sizeof(p_bits));
        g_string_append_printf(text, "%u %u %u %u %u %u %016llx",
                               factor->stage, factor->rule,
                               factor->potential_kind, factor->negative,
                               factor->head_idx, ref->num_vars,
                               (unsigned long long)p_bits);
        for (uint32_t j = 0; j < ref->num_vars; j++) {
            g_string_append_printf(text, " %u", ref->local_vars[j]);
        }
        g_string_append_c(text, '\n');
    }

    g_string_append_printf(text, "COMPONENTS %u\n", base->components->len);
    for (guint i = 0; i < base->components->len; i++) {
        const OspreyExactComponent *component = g_ptr_array_index(
            base->components, i);
        g_string_append_printf(text, "C %u", i);
        for (guint j = 0; j < component->local_vars->len; j++) {
            g_string_append_printf(text, " v%u",
                                   g_array_index(component->local_vars,
                                                 uint32_t, j));
        }
        g_string_append(text, " f");
        for (guint j = 0; j < component->factor_refs->len; j++) {
            g_string_append_printf(text, " %u",
                                   g_array_index(component->factor_refs,
                                                 uint32_t, j));
        }
        g_string_append_c(text, '\n');
    }
    return g_string_free(text, FALSE);
}

static void test_stage_selection(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t a = add_primitive(ctx, region, 0);
    uint32_t b = add_primitive(ctx, region, 8);
    uint32_t c = add_primitive(ctx, region, 16);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, a);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, b);
    add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA, a, b);
    add_implication(ctx, OSPREY_RULE_CB02, OSPREY_GRAPH_SECONDARY, a, c);

    OspreyExactBase *base = NULL;
    CHECK(osprey_exact_base_build(ctx, &base) == OSPREY_OK,
          "CA-only projection succeeds");
    CHECK(base != NULL && base->graph_var_ids->len == 2 &&
          base->factor_refs->len == 3 && base->components->len == 1,
          "only CA factors and incident variables are retained");
    for (guint i = 0; base != NULL && i < base->factor_refs->len; i++) {
        OspreyExactFactorRef *ref = &g_array_index(base->factor_refs,
                                                   OspreyExactFactorRef, i);
        OspreyFactor *factor = g_array_index(ctx->graph->factors,
                                             OspreyFactor *,
                                             ref->graph_factor_id);
        CHECK(factor->stage == OSPREY_GRAPH_BASE_CA,
              "secondary factor is absent from projection");
    }
    OspreyExactTopology *topology = NULL;
    CHECK(base != NULL &&
          osprey_exact_topology_build(ctx, base, &topology) == OSPREY_OK &&
          topology != NULL,
          "secondary-only variables remain outside exact topology");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_late_ca08(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyAddress base_address = { region, 0 };
    uint32_t scalar = add_scalar(ctx, region, 0);
    uint32_t field = add_field(ctx, region, 0, base_address);
    add_implication(ctx, OSPREY_RULE_CB02, OSPREY_GRAPH_SECONDARY,
                    scalar, field);
    OspreyFactorBatchResult batch = osprey_factor_add_bidirectional(
        ctx, OSPREY_RULE_CA08, OSPREY_GRAPH_BASE_CA, true, 0.2,
        scalar, field);
    CHECK(batch.status == OSPREY_OK && batch.inserted == 2,
          "late CA08 factors inserted");

    OspreyExactBase *base = NULL;
    CHECK(osprey_exact_base_build(ctx, &base) == OSPREY_OK,
          "late CA08 projection succeeds");
    CHECK(base != NULL && base->graph_var_ids->len == 2 &&
          base->factor_refs->len == 2 && base->components->len == 1,
          "late-created FieldOf variable remains in base projection");
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_secondary_contamination(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t a = add_primitive(ctx, region, 0);
    uint32_t b = add_primitive(ctx, region, 8);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, a);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, b);
    add_implication(ctx, OSPREY_RULE_CB02, OSPREY_GRAPH_SECONDARY, a, b);

    OspreyExactBase *base = NULL;
    CHECK(osprey_exact_base_build(ctx, &base) == OSPREY_OK,
          "secondary contamination projection succeeds");
    CHECK(base != NULL && base->components->len == 2,
          "secondary factor cannot merge CA components");
    OspreyExactTopology *topology = NULL;
    CHECK(base != NULL &&
          osprey_exact_topology_build(ctx, base, &topology) == OSPREY_OK &&
          topology != NULL && topology->components->len == 2,
          "secondary factor cannot contaminate topology");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_ca05_bridge(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyRegionId stack = make_region(OSPREY_REGION_STACK_FUNCTION, 0x100);
    uint32_t global_access = add_primitive_access(ctx, global, 0, 0x20);
    uint32_t stack_var = add_primitive(ctx, stack, -8);
    add_implication(ctx, OSPREY_RULE_CA05, OSPREY_GRAPH_BASE_CA,
                    global_access, stack_var);

    OspreyExactBase *base = NULL;
    CHECK(osprey_exact_base_build(ctx, &base) == OSPREY_OK,
          "CA05 bridge projection succeeds");
    CHECK(base != NULL && base->graph_var_ids->len == 2 &&
          base->components->len == 1,
          "CA05 bridges regions by actual factor connectivity");
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_unary_components(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t a = add_primitive(ctx, region, 0);
    uint32_t b = add_primitive(ctx, region, 8);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, a);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, b);

    OspreyExactBase *base = NULL;
    CHECK(osprey_exact_base_build(ctx, &base) == OSPREY_OK,
          "unary projection succeeds");
    CHECK(base != NULL && base->components->len == 2,
          "independent unary factors form independent components");
    for (guint i = 0; base != NULL && i < base->components->len; i++) {
        OspreyExactComponent *component = g_ptr_array_index(base->components, i);
        CHECK(component->local_vars->len == 1 &&
              component->factor_refs->len == 1,
              "unary component has one variable and one factor");
    }
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_complete_map_initialization(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t first = add_primitive(ctx, region, 0);
    uint32_t interior = add_primitive(ctx, region, 8);
    uint32_t outside = add_primitive(ctx, region, 16);
    uint32_t last = add_primitive(ctx, region, 24);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, first);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, last);
    add_implication(ctx, OSPREY_RULE_CB02, OSPREY_GRAPH_SECONDARY,
                    interior, outside);

    g_array_index(ctx->graph->vars, OspreyVar, first).belief = 0.37;
    g_array_index(ctx->graph->vars, OspreyVar, last).belief = 0.63;
    OspreyExactBase *base = NULL;
    CHECK(osprey_exact_base_build(ctx, &base) == OSPREY_OK,
          "complete-map projection succeeds");
    CHECK(base != NULL && base->graph_var_count == 4 &&
          base->local_by_graph[interior] == UINT32_MAX &&
          base->local_by_graph[outside] == UINT32_MAX &&
          base->local_by_graph[first] != UINT32_MAX &&
          base->local_by_graph[last] != UINT32_MAX,
          "every production variable has an initialized local-map entry");
    CHECK(fabs(g_array_index(ctx->graph->vars, OspreyVar, first).belief - 0.37) < 1e-12 &&
          fabs(g_array_index(ctx->graph->vars, OspreyVar, last).belief - 0.63) < 1e-12,
          "projection does not publish beliefs");
    CHECK(base != NULL && component_for_local(
              base, base->local_by_graph[first]) != NULL &&
          component_for_local(base, base->local_by_graph[last]) != NULL,
          "factors outside a component are not scanned into it");
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_accepted_predicate_order(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_STACK_FUNCTION, 0x100);
    uint32_t zero = add_primitive(ctx, region, 0);
    uint32_t negative = add_primitive(ctx, region, -8);
    uint32_t late_pc = add_primitive_access(ctx, region, 0, 2);
    uint32_t early_pc = add_primitive_access(ctx, region, 8, 1);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, zero);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, negative);
    add_implication(ctx, OSPREY_RULE_CA04, OSPREY_GRAPH_BASE_CA,
                    zero, late_pc);
    add_implication(ctx, OSPREY_RULE_CA04, OSPREY_GRAPH_BASE_CA,
                    negative, early_pc);

    OspreyExactBase *base = NULL;
    CHECK(osprey_exact_base_build(ctx, &base) == OSPREY_OK,
          "accepted-order projection succeeds");
    CHECK(base != NULL && base->graph_var_ids->len == 4 &&
          g_array_index(base->graph_var_ids, uint32_t, 0) == negative &&
          g_array_index(base->graph_var_ids, uint32_t, 1) == zero &&
          g_array_index(base->graph_var_ids, uint32_t, 2) == early_pc &&
          g_array_index(base->graph_var_ids, uint32_t, 3) == late_pc,
          "local IDs use signed offsets and PrimitiveAccess PC-first order");
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static bool next_permutation(unsigned *values, size_t count)
{
    size_t pivot = count - 1;
    while (pivot > 0 && values[pivot - 1] >= values[pivot]) pivot--;
    if (pivot == 0) return false;

    size_t successor = count - 1;
    while (values[successor] <= values[pivot - 1]) successor--;
    unsigned tmp = values[pivot - 1];
    values[pivot - 1] = values[successor];
    values[successor] = tmp;
    for (size_t end = count - 1; pivot < end; pivot++, end--) {
        tmp = values[pivot];
        values[pivot] = values[end];
        values[end] = tmp;
    }
    return true;
}

static char *build_permutation_dump(const unsigned variable_order[3],
                                    const unsigned factor_order[5])
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    int64_t offsets[3] = { -8, 0, 8 };
    uint32_t ids[3];
    for (unsigned i = 0; i < 3; i++) {
        unsigned index = variable_order[i];
        ids[index] = add_primitive(ctx, region, offsets[index]);
    }
    for (unsigned i = 0; i < 5; i++) {
        switch (factor_order[i]) {
        case 0:
        case 1:
        case 2:
            add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                      ids[factor_order[i]]);
            break;
        case 3:
            add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                            ids[0], ids[1]);
            break;
        case 4:
            add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                            ids[1], ids[2]);
            break;
        default:
            CHECK(false, "factor permutation index is valid");
            break;
        }
    }

    OspreyExactBase *base = NULL;
    OspreyExactTopology *topology = NULL;
    CHECK(osprey_exact_base_build(ctx, &base) == OSPREY_OK,
          "permutation projection succeeds");
    CHECK(base != NULL &&
          osprey_exact_topology_build(ctx, base, &topology) == OSPREY_OK &&
          topology != NULL,
          "permutation topology succeeds");
    char *projection = base == NULL ? g_strdup("") : projection_dump(ctx, base);
    char *topology_text = topology == NULL ? g_strdup("") :
        topology_dump(topology);
    CHECK(osprey_stage4_exact(ctx) == OSPREY_OK,
          "permutation exact inference succeeds");
    char *beliefs = g_strdup_printf(
        "BELIEFS %a %a %a\n",
        g_array_index(ctx->graph->vars, OspreyVar, ids[0]).belief,
        g_array_index(ctx->graph->vars, OspreyVar, ids[1]).belief,
        g_array_index(ctx->graph->vars, OspreyVar, ids[2]).belief);
    char *dump = g_strconcat(projection, topology_text, beliefs, NULL);
    g_free(projection);
    g_free(topology_text);
    g_free(beliefs);
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);
    return dump;
}

static void test_insertion_permutations(void)
{
    unsigned variable_order[3] = { 0, 1, 2 };
    char *expected = NULL;
    unsigned cases = 0;
    do {
        unsigned factor_order[5] = { 0, 1, 2, 3, 4 };
        do {
            char *actual = build_permutation_dump(variable_order,
                                                   factor_order);
            if (expected == NULL) {
                expected = actual;
            } else {
                CHECK(strcmp(expected, actual) == 0,
                      "projection and topology ignore insertion order");
                g_free(actual);
            }
            cases++;
        } while (next_permutation(factor_order,
                                  G_N_ELEMENTS(factor_order)));
    } while (next_permutation(variable_order, G_N_ELEMENTS(variable_order)));
    CHECK(cases == 720, "all variable/factor insertion permutations execute");
    g_free(expected);
}

static OspreyStatus build_mutated_graph(unsigned mutation)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t a = add_primitive(ctx, region, 0);
    uint32_t b = add_primitive(ctx, region, 8);
    uint32_t c = add_primitive(ctx, region, 16);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, a);
    add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA, a, b);
    OspreyFactor *factor = g_array_index(ctx->graph->factors,
                                         OspreyFactor *, 1);
    OspreyFactor *detached = NULL;
    switch (mutation) {
    case 0:
        factor->stage = 99;
        break;
    case 1:
        factor->rule = OSPREY_RULE_CB02;
        break;
    case 2:
        factor->head_idx = 2;
        break;
    case 3:
        factor->num_vars = OSPREY_FACTOR_MAX_ARITY + 1;
        break;
    case 4:
        factor->p = NAN;
        break;
    case 5:
        g_array_index(ctx->graph->vars, OspreyVar, b).id = 99;
        break;
    case 6:
        detached = factor;
        g_array_index(ctx->graph->factors, OspreyFactor *, 1) = NULL;
        break;
    case 7:
        factor->rule = OSPREY_RULE_CA01;
        break;
    case 8:
        factor->rule = OSPREY_RULE_CA04;
        break;
    case 9:
        factor->var_ids = g_renew(uint32_t, factor->var_ids, 3);
        factor->var_ids[0] = a;
        factor->var_ids[1] = b;
        factor->var_ids[2] = c;
        factor->num_vars = 3;
        factor->head_idx = 2;
        break;
    default:
        break;
    }
    OspreyExactBase *base = NULL;
    OspreyStatus status = osprey_exact_base_build(ctx, &base);
    CHECK(base == NULL, "malformed projection does not return partial ownership");
    osprey_exact_base_free(base);
    if (detached != NULL) {
        g_free(detached->var_ids);
        g_free(detached);
    }
    osprey_free(ctx);
    return status;
}

static void test_malformed_graphs(void)
{
    for (unsigned mutation = 0; mutation < 10; mutation++) {
        CHECK(build_mutated_graph(mutation) == OSPREY_INVALID_GRAPH,
              "malformed stage/factor/ID input rejects before topology");
    }

    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t id = add_primitive(ctx, region, 0);
    OspreyVar duplicate = g_array_index(ctx->graph->vars, OspreyVar, id);
    duplicate.id = 1;
    g_array_append_val(ctx->graph->vars, duplicate);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, id);
    OspreyExactBase *base = NULL;
    CHECK(osprey_exact_base_build(ctx, &base) == OSPREY_INVALID_GRAPH &&
          base == NULL, "duplicate full predicate keys reject");
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_empty_base(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t a = add_primitive(ctx, region, 0);
    add_prior(ctx, OSPREY_RULE_CB01, OSPREY_GRAPH_SECONDARY, a);
    OspreyExactBase *base = NULL;
    CHECK(osprey_exact_base_build(ctx, &base) == OSPREY_INCOMPLETE_FACTS &&
          base == NULL, "secondary-only graph has no exact base input");
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_repeated_ownership(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t a = add_primitive(ctx, region, 0);
    uint32_t b = add_primitive(ctx, region, 8);
    add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA, a, b);
    for (unsigned i = 0; i < 100; i++) {
        OspreyExactBase *base = NULL;
        CHECK(osprey_exact_base_build(ctx, &base) == OSPREY_OK && base != NULL,
              "repeated projection build succeeds");
        osprey_exact_base_free(base);
    }
    osprey_free(ctx);
}

static OspreyStatus build_test_topology(OspreyContext *ctx,
                                        OspreyExactBase **base_out,
                                        OspreyExactTopology **topology_out)
{
    OspreyStatus status;
    *base_out = NULL;
    *topology_out = NULL;
    status = osprey_exact_base_build(ctx, base_out);
    if (status != OSPREY_OK) return status;
    status = osprey_exact_topology_build(ctx, *base_out, topology_out);
    return status;
}

static void add_path_graph(OspreyContext *ctx, uint32_t *ids,
                           unsigned count)
{
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    for (unsigned i = 0; i < count; i++) {
        ids[i] = add_primitive(ctx, region, (int64_t)i * 8);
        add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, ids[i]);
        if (i != 0) {
            add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                            ids[i - 1], ids[i]);
        }
    }
}

static char *topology_dump(const OspreyExactTopology *topology)
{
    GString *text = g_string_new("");
    for (guint i = 0; i < topology->components->len; i++) {
        const OspreyExactTopologyComponent *component = g_ptr_array_index(
            topology->components, i);
        g_string_append_printf(text, "C %u V", i);
        for (guint j = 0; j < component->local_vars->len; j++) {
            g_string_append_printf(text, " %u",
                                   g_array_index(component->local_vars,
                                                 uint32_t, j));
        }
        g_string_append(text, " O");
        for (guint j = 0; j < component->elimination_order->len; j++) {
            g_string_append_printf(text, " %u",
                                   g_array_index(component->elimination_order,
                                                 uint32_t, j));
        }
        g_string_append(text, " M");
        for (guint j = 0; j < component->cliques->len; j++) {
            const OspreyExactClique *clique = g_ptr_array_index(
                component->cliques, j);
            g_string_append(text, " [");
            for (guint k = 0; k < clique->local_vars->len; k++) {
                g_string_append_printf(text, "%s%u", k == 0 ? "" : ",",
                                       g_array_index(clique->local_vars,
                                                     uint32_t, k));
            }
            g_string_append(text, "]{");
            for (guint k = 0; k < clique->factor_refs->len; k++) {
                g_string_append_printf(text, "%s%u", k == 0 ? "" : ",",
                                       g_array_index(clique->factor_refs,
                                                     uint32_t, k));
            }
            g_string_append_c(text, '}');
        }
        g_string_append(text, " E");
        for (guint j = 0; j < component->tree_edges->len; j++) {
            const OspreyExactTreeEdge *edge = &g_array_index(
                component->tree_edges, OspreyExactTreeEdge, j);
            g_string_append_printf(text, " (%u>%u:", edge->parent,
                                   edge->child);
            for (guint k = 0; k < edge->separator->len; k++) {
                g_string_append_printf(text, "%s%u", k == 0 ? "" : ",",
                                       g_array_index(edge->separator,
                                                     uint32_t, k));
            }
            g_string_append_c(text, ')');
        }
        g_string_append_c(text, '\n');
    }
    return g_string_free(text, FALSE);
}

static void test_chain_width_and_order(void)
{
    OspreyConfig config = graph_config();
    config.max_exact_clique_vars = 2;
    OspreyContext *ctx = new_graph_context_with_config(&config);
    OspreyExactBase *base = NULL;
    OspreyExactTopology *topology = NULL;
    uint32_t ids[64];
    add_path_graph(ctx, ids, G_N_ELEMENTS(ids));
    CHECK(build_test_topology(ctx, &base, &topology) == OSPREY_OK,
          "64-variable chain fits induced width two");
    CHECK(topology != NULL && topology->components->len == 1,
          "chain has one exact component");
    if (topology != NULL) {
        OspreyExactTopologyComponent *component = g_ptr_array_index(
            topology->components, 0);
        CHECK(component->elimination_order->len == 64 &&
              component->cliques->len == 63 &&
              component->tree_edges->len == 62,
              "chain records every elimination and maximal clique");
        CHECK(component->max_clique_vars == 2 &&
              topology->max_clique_vars == 2,
              "chain width is two, independent of component size");
        CHECK(component->table_bytes == 4000 &&
              topology->max_component_table_bytes == 4000,
              "64-variable chain plans 4000 bytes of numerical workspace");
        for (unsigned i = 0; i < 64 && i < component->elimination_order->len;
             i++) {
            CHECK(g_array_index(component->elimination_order, uint32_t, i) == i,
                  "chain min-fill tie order is canonical");
        }
        CHECK(osprey_exact_topology_validate(ctx, base, topology),
              "chain topology validates independently");
        for (guint i = 0; i < topology->factor_owner->len; i++) {
            CHECK(g_array_index(topology->factor_owner, uint32_t, i) !=
                      UINT32_MAX,
                  "every chain factor has one owner");
        }
    }
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_width_boundaries(void)
{
    OspreyConfig config = graph_config();
    OspreyContext *ctx;
    OspreyExactBase *base;
    OspreyExactTopology *topology;
    uint32_t ids[4];

    config.max_exact_clique_vars = 1;
    ctx = new_graph_context_with_config(&config);
    add_path_graph(ctx, ids, 4);
    base = NULL;
    topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) ==
              OSPREY_EXACT_COMPONENT_TOO_LARGE && topology == NULL,
          "chain rejects when induced clique width exceeds one");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);

    config.max_exact_clique_vars = 2;
    ctx = new_graph_context_with_config(&config);
    {
        OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
        for (unsigned i = 0; i < 4; i++) {
            ids[i] = add_primitive(ctx, region, (int64_t)i * 8);
            add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, ids[i]);
        }
        add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                        ids[0], ids[1]);
        add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                        ids[1], ids[2]);
        add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                        ids[2], ids[3]);
        add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                        ids[3], ids[0]);
    }
    base = NULL;
    topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) ==
              OSPREY_EXACT_COMPONENT_TOO_LARGE && topology == NULL,
          "four-cycle rejects induced width three at limit two");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);

    config.max_exact_clique_vars = 3;
    ctx = new_graph_context_with_config(&config);
    {
        OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
        for (unsigned i = 0; i < 4; i++) {
            ids[i] = add_primitive(ctx, region, (int64_t)i * 8);
            add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, ids[i]);
        }
        add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                        ids[0], ids[1]);
        add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                        ids[1], ids[2]);
        add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                        ids[2], ids[3]);
        add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                        ids[3], ids[0]);
    }
    base = NULL;
    topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) == OSPREY_OK,
          "four-cycle fits induced width three at limit three");
    CHECK(topology != NULL && topology->max_clique_vars == 3,
          "four-cycle records width three");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void add_complete_four_graph(OspreyContext *ctx, uint32_t ids[4])
{
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    for (unsigned i = 0; i < 4; i++) {
        ids[i] = add_primitive(ctx, region, (int64_t)i * 8);
        add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, ids[i]);
    }
    for (unsigned i = 0; i < 4; i++) {
        for (unsigned j = i + 1; j < 4; j++) {
            add_implication(ctx, OSPREY_RULE_CA02,
                            OSPREY_GRAPH_BASE_CA, ids[i], ids[j]);
        }
    }
}

static void test_width_four_clique(void)
{
    OspreyConfig config = graph_config();
    uint32_t ids[4];
    OspreyContext *ctx;
    OspreyExactBase *base;
    OspreyExactTopology *topology;

    config.max_exact_clique_vars = 3;
    ctx = new_graph_context_with_config(&config);
    add_complete_four_graph(ctx, ids);
    base = NULL;
    topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) ==
              OSPREY_EXACT_COMPONENT_TOO_LARGE && topology == NULL,
          "four-variable clique rejects at width limit three");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);

    config.max_exact_clique_vars = 4;
    ctx = new_graph_context_with_config(&config);
    add_complete_four_graph(ctx, ids);
    base = NULL;
    topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) == OSPREY_OK,
          "four-variable clique fits width limit four");
    CHECK(topology != NULL && topology->max_clique_vars == 4 &&
          topology->components->len == 1 &&
          ((OspreyExactTopologyComponent *)g_ptr_array_index(
              topology->components, 0))->cliques->len == 1,
          "four-variable graph records one width-four clique");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_star_and_unary_topology(void)
{
    OspreyConfig config = graph_config();
    OspreyContext *ctx = new_graph_context_with_config(&config);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t center = add_primitive(ctx, region, 0);
    uint32_t leaves[8];
    for (unsigned i = 0; i < G_N_ELEMENTS(leaves); i++) {
        leaves[i] = add_primitive(ctx, region, (int64_t)(i + 1) * 8);
        add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, leaves[i]);
        add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                        leaves[i], center);
    }
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, center);
    OspreyExactBase *base = NULL;
    OspreyExactTopology *topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) == OSPREY_OK,
          "star fits induced width two");
    CHECK(topology != NULL && topology->max_clique_vars == 2 &&
          g_ptr_array_index(topology->components, 0) != NULL,
          "star leaves eliminate before center");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);

    ctx = new_graph_context_with_config(&config);
    for (unsigned i = 0; i < 3; i++) {
        uint32_t id = add_primitive(ctx, region, (int64_t)i * 8);
        add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, id);
    }
    config.max_exact_clique_vars = 1;
    /* The direct context retains the original config; use a fresh one for
     * the limit check so independent unary components remain explicit. */
    osprey_free(ctx);
    ctx = new_graph_context_with_config(&config);
    for (unsigned i = 0; i < 3; i++) {
        uint32_t id = add_primitive(ctx, region, (int64_t)i * 8);
        add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, id);
    }
    base = NULL;
    topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) == OSPREY_OK,
          "independent unary components fit limit one");
    CHECK(topology != NULL && topology->components->len == 3,
          "unary factors remain separate components");
    if (topology != NULL) {
        for (guint i = 0; i < topology->components->len; i++) {
            OspreyExactTopologyComponent *component = g_ptr_array_index(
                topology->components, i);
            CHECK(component->cliques->len == 1 &&
                  component->tree_edges->len == 0,
                  "unary component has one clique and no edge");
        }
    }
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_reference_topology_oracle(void)
{
    OspreyConfig config = graph_config();
    OspreyContext *ctx = new_graph_context_with_config(&config);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t center = add_primitive(ctx, region, 0);
    uint32_t leaves[4];
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, center);
    for (unsigned i = 0; i < G_N_ELEMENTS(leaves); i++) {
        leaves[i] = add_primitive(ctx, region, (int64_t)(i + 1) * 8);
        add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, leaves[i]);
        add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                        leaves[i], center);
    }
    OspreyExactBase *base = NULL;
    OspreyExactTopology *topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) == OSPREY_OK &&
          stage4_exact_reference_validate(base, topology),
          "independent oracle matches tied star topology");
    if (topology != NULL) {
        OspreyExactTopologyComponent *component = g_ptr_array_index(
            topology->components, 0);
        CHECK(component->cliques->len == 4 &&
              component->tree_edges->len == 3,
              "star produces four maximal cliques and one tree");
        for (guint i = 0; i < component->tree_edges->len; i++) {
            OspreyExactTreeEdge *edge = &g_array_index(
                component->tree_edges, OspreyExactTreeEdge, i);
            CHECK(edge->parent == 0 && edge->child == i + 1 &&
                  edge->separator->len == 1 &&
                  g_array_index(edge->separator, uint32_t, 0) == 0,
                  "equal-weight clique-tree ties use canonical edges");
        }
    }
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);

    config.max_exact_clique_vars = 3;
    ctx = new_graph_context_with_config(&config);
    uint32_t ids[4];
    for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) {
        ids[i] = add_primitive(ctx, region, (int64_t)i * 8);
        add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, ids[i]);
    }
    for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) {
        add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                        ids[i], ids[(i + 1) % G_N_ELEMENTS(ids)]);
    }
    base = NULL;
    topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) == OSPREY_OK &&
          stage4_exact_reference_validate(base, topology),
          "independent oracle matches induced four-cycle topology");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_cross_region_and_late_topology(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyRegionId stack = make_region(OSPREY_REGION_STACK_FUNCTION, 0x100);
    uint32_t access = add_primitive_access(ctx, global, 0, 0x20);
    uint32_t value = add_primitive(ctx, stack, -8);
    add_implication(ctx, OSPREY_RULE_CA05, OSPREY_GRAPH_BASE_CA,
                    access, value);
    OspreyExactBase *base = NULL;
    OspreyExactTopology *topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) == OSPREY_OK,
          "cross-region CA05 topology succeeds");
    CHECK(topology != NULL && topology->components->len == 1 &&
          ((OspreyExactTopologyComponent *)g_ptr_array_index(
              topology->components, 0))->cliques->len == 1,
          "cross-region CA05 remains one connected clique");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);

    ctx = new_graph_context();
    OspreyAddress address = { global, 0 };
    uint32_t scalar = add_scalar(ctx, global, 0);
    uint32_t field = add_field(ctx, global, 0, address);
    add_implication(ctx, OSPREY_RULE_CB02, OSPREY_GRAPH_SECONDARY,
                    scalar, field);
    OspreyFactorBatchResult batch = osprey_factor_add_bidirectional(
        ctx, OSPREY_RULE_CA08, OSPREY_GRAPH_BASE_CA, true, 0.2,
        scalar, field);
    CHECK(batch.status == OSPREY_OK, "late CA08 factors remain accepted");
    base = NULL;
    topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) == OSPREY_OK,
          "late CA08 topology succeeds");
    CHECK(topology != NULL && topology->components->len == 1 &&
          topology->factor_owner->len == 2,
          "late CA08 field is included in exact topology");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_topology_determinism_and_validator(void)
{
    OspreyConfig config = graph_config();
    OspreyContext *first = new_graph_context_with_config(&config);
    OspreyContext *second = new_graph_context_with_config(&config);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t a[4];
    uint32_t b[4];
    for (unsigned i = 0; i < 4; i++) {
        a[i] = add_primitive(first, region, (int64_t)i * 8);
        add_prior(first, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, a[i]);
    }
    for (unsigned i = 4; i-- > 0;) {
        b[i] = add_primitive(second, region, (int64_t)i * 8);
        add_prior(second, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, b[i]);
    }
    add_implication(first, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA, a[0], a[1]);
    add_implication(first, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA, a[1], a[2]);
    add_implication(first, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA, a[2], a[3]);
    add_implication(second, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA, b[2], b[3]);
    add_implication(second, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA, b[1], b[2]);
    add_implication(second, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA, b[0], b[1]);
    OspreyExactBase *base_a = NULL;
    OspreyExactBase *base_b = NULL;
    OspreyExactTopology *topology_a = NULL;
    OspreyExactTopology *topology_b = NULL;
    CHECK(build_test_topology(first, &base_a, &topology_a) == OSPREY_OK &&
          build_test_topology(second, &base_b, &topology_b) == OSPREY_OK,
          "topology insertion permutations succeed");
    if (topology_a != NULL && topology_b != NULL) {
        char *dump_a = topology_dump(topology_a);
        char *dump_b = topology_dump(topology_b);
        CHECK(strcmp(dump_a, dump_b) == 0,
              "cliques, separators, owners, and roots are deterministic");
        g_free(dump_a);
        g_free(dump_b);
        CHECK(osprey_exact_topology_validate(first, base_a, topology_a) &&
              osprey_exact_topology_validate(second, base_b, topology_b),
              "both permutation topologies validate");
    }
    osprey_exact_topology_free(topology_a);
    osprey_exact_topology_free(topology_b);
    osprey_exact_base_free(base_a);
    osprey_exact_base_free(base_b);
    osprey_free(first);
    osprey_free(second);

    OspreyContext *ctx = new_graph_context();
    uint32_t ids[3];
    add_path_graph(ctx, ids, 3);
    OspreyExactBase *base = NULL;
    OspreyExactTopology *topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) == OSPREY_OK,
          "validator fixture builds");
    if (topology != NULL) {
        OspreyExactTopologyComponent *component = g_ptr_array_index(
            topology->components, 0);
        if (component->tree_edges->len != 0) {
            OspreyExactTreeEdge *edge = &g_array_index(
                component->tree_edges, OspreyExactTreeEdge, 0);
            uint32_t saved = g_array_index(edge->separator, uint32_t, 0);
            g_array_index(edge->separator, uint32_t, 0) = UINT32_MAX;
            CHECK(!osprey_exact_topology_validate(ctx, base, topology),
                  "validator rejects a corrupted separator");
            g_array_index(edge->separator, uint32_t, 0) = saved;
        }
        uint32_t saved_owner = g_array_index(topology->factor_owner,
                                              uint32_t, 0);
        g_array_index(topology->factor_owner, uint32_t, 0) = UINT32_MAX;
        CHECK(!osprey_exact_topology_validate(ctx, base, topology),
              "validator rejects an unassigned factor owner");
        g_array_index(topology->factor_owner, uint32_t, 0) = saved_owner;

        OspreyFactorResult added = osprey_factor_add_implication(
            ctx, OSPREY_RULE_CA03, OSPREY_GRAPH_BASE_CA, true, 0.2,
            &ids[0], 1, ids[1]);
        CHECK(added.status == OSPREY_OK && added.inserted,
              "stale-projection fixture adds a valid base factor");
        CHECK(!osprey_exact_topology_validate(ctx, base, topology),
              "validator rejects a projection missing a base factor");
    }
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);

    ctx = new_graph_context();
    uint32_t chordal[5];
    for (unsigned i = 0; i < G_N_ELEMENTS(chordal); i++) {
        chordal[i] = add_primitive(ctx, region, (int64_t)i * 8);
        add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, chordal[i]);
    }
    const uint32_t chordal_edges[][2] = {
        { 0, 1 }, { 0, 2 }, { 1, 2 },
        { 0, 3 }, { 1, 3 },
        { 0, 4 }, { 2, 4 },
    };
    for (unsigned i = 0; i < G_N_ELEMENTS(chordal_edges); i++) {
        add_implication(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                        chordal[chordal_edges[i][0]],
                        chordal[chordal_edges[i][1]]);
    }
    base = NULL;
    topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) == OSPREY_OK &&
          stage4_exact_reference_validate(base, topology),
          "running-intersection fixture matches the independent oracle");
    if (topology != NULL) {
        OspreyExactTopologyComponent *component = g_ptr_array_index(
            topology->components, 0);
        CHECK(component->cliques->len == 3 &&
              component->tree_edges->len == 2,
              "running-intersection fixture has three maximal cliques");
        if (component->tree_edges->len == 2) {
            OspreyExactTreeEdge *edge = &g_array_index(
                component->tree_edges, OspreyExactTreeEdge, 1);
            CHECK(edge->left == 0 && edge->right == 2 &&
                  edge->parent == 0 && edge->child == 2 &&
                  edge->separator != NULL && edge->separator->len == 2,
                  "fixture starts from the canonical maximum-weight tree");
            if (edge->separator == NULL || edge->separator->len != 2) {
                goto invalid_tree_fixture;
            }
            uint32_t saved_left = edge->left;
            uint32_t saved_right = edge->right;
            uint32_t saved_parent = edge->parent;
            uint32_t saved_child = edge->child;
            uint32_t saved_separator[2] = {
                g_array_index(edge->separator, uint32_t, 0),
                g_array_index(edge->separator, uint32_t, 1),
            };
            edge->left = 1;
            edge->right = 2;
            edge->parent = 1;
            edge->child = 2;
            g_array_set_size(edge->separator, 0);
            uint32_t zero = 0;
            g_array_append_val(edge->separator, zero);
            CHECK(!osprey_exact_topology_validate(ctx, base, topology),
                  "validator rejects a disconnected variable-clique subtree");
            edge->left = saved_left;
            edge->right = saved_right;
            edge->parent = saved_parent;
            edge->child = saved_child;
            g_array_set_size(edge->separator, 0);
            g_array_append_vals(edge->separator, saved_separator,
                                G_N_ELEMENTS(saved_separator));
        }
    }
invalid_tree_fixture:
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void restore_env(const char *name, const char *value)
{
    if (value != NULL) {
        g_setenv(name, value, TRUE);
    } else {
        g_unsetenv(name);
    }
}

static void test_exact_configuration(void)
{
    const char *factor_name = "BINRADAR_OSPREY_MAX_FACTORS";
    const char *clique_name = "BINRADAR_OSPREY_MAX_EXACT_CLIQUE_VARS";
    const char *table_name = "BINRADAR_OSPREY_MAX_EXACT_TABLE_MB";
    char *saved_factor = g_strdup(g_getenv(factor_name));
    char *saved_clique = g_strdup(g_getenv(clique_name));
    char *saved_table = g_strdup(g_getenv(table_name));
    OspreyConfig config;

    g_setenv(factor_name, "1234", TRUE);
    g_unsetenv(clique_name);
    g_setenv(table_name, "1", TRUE);
    CHECK(osprey_config_from_env(&config) &&
          config.max_factors == 1234 &&
          config.max_exact_clique_vars == 20 &&
          config.max_exact_table_bytes == 1024u * 1024u,
          "exact limits parse independently of preceding optional values");

    restore_env(factor_name, saved_factor);
    restore_env(clique_name, saved_clique);
    restore_env(table_name, saved_table);
    g_free(saved_factor);
    g_free(saved_clique);
    g_free(saved_table);
}

static void test_workspace_budget(void)
{
    OspreyConfig config = graph_config();
    config.max_exact_table_bytes = sizeof(double) - 1;
    OspreyContext *ctx = new_graph_context_with_config(&config);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t id = add_primitive(ctx, region, 0);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, id);
    OspreyExactBase *base = NULL;
    OspreyExactTopology *topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) ==
              OSPREY_EXACT_COMPONENT_TOO_LARGE && topology == NULL,
          "exact table workspace budget rejects before numerical allocation");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);

    config = graph_config();
    config.max_exact_table_bytes = 159;
    ctx = new_graph_context_with_config(&config);
    uint32_t ids[4];
    add_path_graph(ctx, ids, G_N_ELEMENTS(ids));
    base = NULL;
    topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) ==
              OSPREY_EXACT_COMPONENT_TOO_LARGE && topology == NULL,
          "cumulative clique and separator workspace rejects one byte low");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);

    config = graph_config();
    config.max_exact_table_bytes = 160;
    ctx = new_graph_context_with_config(&config);
    add_path_graph(ctx, ids, G_N_ELEMENTS(ids));
    base = NULL;
    topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) == OSPREY_OK &&
          topology != NULL && topology->table_bytes == 160 &&
          topology->max_component_table_bytes == 160,
          "exact cumulative workspace succeeds at the checked boundary");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);

    config = graph_config();
    config.max_exact_clique_vars = sizeof(size_t) * 8;
    ctx = new_graph_context_with_config(&config);
    id = add_primitive(ctx, region, 0);
    add_prior(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, id);
    base = NULL;
    topology = NULL;
    CHECK(build_test_topology(ctx, &base, &topology) ==
              OSPREY_EXACT_COMPONENT_TOO_LARGE && topology == NULL,
          "unrepresentable exact width rejects safely");
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);
}

static void test_exact_log_arithmetic(void)
{
    double out = 0.0;
    double log_norm = 0.0;
    double table[3] = { log(0.2), log(0.3), -INFINITY };
    double impossible[2] = { -INFINITY, -INFINITY };
    double finite_underflow[2] = { -DBL_MAX, DBL_MAX };
    double normalized_sum = -INFINITY;

    CHECK(osprey_logaddexp(-INFINITY, -INFINITY, &out) &&
              out == -INFINITY,
          "logaddexp preserves two exact zero weights");
    CHECK(osprey_logaddexp(log(0.2), -INFINITY, &out) &&
              fabs(out - log(0.2)) < 1e-15,
          "logaddexp handles one exact zero weight");
    CHECK(osprey_log_product_add(log(0.2), log(0.3), &out) &&
              fabs(out - log(0.06)) < 1e-15,
          "log product addition preserves assignment products");
    CHECK(osprey_log_product_add(-INFINITY, 0.0, &out) &&
              out == -INFINITY,
          "log product addition preserves exact zero support");
    CHECK(!osprey_log_product_add(-DBL_MAX, -DBL_MAX, &out),
          "finite log-product underflow rejects instead of becoming hard zero");
    CHECK(!osprey_logaddexp(NAN, 0.0, &out) &&
              !osprey_logaddexp(INFINITY, 0.0, &out),
          "logaddexp rejects NaN and positive infinity");
    CHECK(osprey_log_normalize(table, G_N_ELEMENTS(table), &log_norm) &&
              fabs(log_norm - log(0.5)) < 1e-15,
          "log normalization returns the stable log partition");
    for (unsigned i = 0; i < G_N_ELEMENTS(table); i++) {
        CHECK(table[i] == -INFINITY ||
                  (isfinite(table[i]) && table[i] <= 0.0),
              "normalized log table retains finite nonpositive entries");
        CHECK(osprey_logaddexp(normalized_sum, table[i],
                                     &normalized_sum),
              "normalized entries have valid log support");
    }
    CHECK(fabs(normalized_sum) < 1e-15,
          "normalized log table sums to one");
    CHECK(!osprey_log_normalize(impossible,
                                      G_N_ELEMENTS(impossible), &log_norm),
          "all-zero table rejects during normalization");
    CHECK(!osprey_log_normalize(finite_underflow,
                                G_N_ELEMENTS(finite_underflow), &log_norm),
          "finite normalization underflow rejects instead of becoming hard zero");
}

static void test_exact_numeric_marginals(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t a = add_primitive(ctx, region, 0);
    uint32_t b = add_primitive(ctx, region, 8);
    uint32_t secondary = add_primitive(ctx, region, 16);
    double p_a = 0.6;
    double p_b = 0.4;
    double p_edge = 0.8;
    uint32_t antecedent = a;
    double w00 = (1.0 - p_a) * (1.0 - p_b) * p_edge;
    double w01 = (1.0 - p_a) * p_b * p_edge;
    double w10 = p_a * (1.0 - p_b) * (1.0 - p_edge);
    double w11 = p_a * p_b * p_edge;
    double partition = w00 + w01 + w10 + w11;
    double expected_a = (w10 + w11) / partition;
    double expected_b = (w01 + w11) / partition;

    add_prior_probability(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                          p_a, a);
    add_prior_probability(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                          p_b, b);
    add_implication_probability(ctx, OSPREY_RULE_CA02,
                                OSPREY_GRAPH_BASE_CA, false, p_edge,
                                &antecedent, 1, b);
    add_implication_probability(ctx, OSPREY_RULE_CB02,
                                OSPREY_GRAPH_SECONDARY, false, p_edge,
                                &antecedent, 1, secondary);
    g_array_index(ctx->graph->vars, OspreyVar, secondary).belief = 0.37;

    CHECK(osprey_stage4_exact(ctx) == OSPREY_OK,
          "exact sum-product computes a connected base component");
    CHECK(fabs(g_array_index(ctx->graph->vars, OspreyVar, a).belief -
               expected_a) < 1e-12,
          "exact marginal matches the two-variable joint distribution");
    CHECK(fabs(g_array_index(ctx->graph->vars, OspreyVar, b).belief -
               expected_b) < 1e-12,
          "exact marginal matches the implication target distribution");
    CHECK(fabs(g_array_index(ctx->graph->vars, OspreyVar, secondary).belief -
               0.37) < 1e-12 &&
              g_array_index(ctx->graph->vars, OspreyVar, secondary).belief_valid == 0,
          "secondary-only beliefs are not initialized by Stage 4");
    CHECK(g_array_index(ctx->graph->vars, OspreyVar, a).belief_valid == 1 &&
              g_array_index(ctx->graph->vars, OspreyVar, b).belief_valid == 1,
          "Stage 4 publishes validity for every exact variable");
    osprey_free(ctx);
}

static void test_exact_extreme_support(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t ids[5];
    const double probabilities[5] = {
        0.0, 1.0, 0.5, DBL_MIN, nextafter(1.0, 0.0)
    };

    for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) {
        ids[i] = add_primitive(ctx, region, (int64_t)i * 8);
        add_prior_probability(ctx, OSPREY_RULE_CA01,
                              OSPREY_GRAPH_BASE_CA, probabilities[i], ids[i]);
    }
    CHECK(osprey_stage4_exact(ctx) == OSPREY_OK,
          "exact inference retains finite and hard-zero priors");
    CHECK(g_array_index(ctx->graph->vars, OspreyVar, ids[0]).belief == 0.0,
          "p=0 prior produces an exact zero marginal");
    CHECK(g_array_index(ctx->graph->vars, OspreyVar, ids[1]).belief == 1.0,
          "p=1 prior produces an exact one marginal");
    CHECK(fabs(g_array_index(ctx->graph->vars, OspreyVar, ids[2]).belief -
               0.5) < 1e-15,
          "p=0.5 prior remains symmetric");
    CHECK(g_array_index(ctx->graph->vars, OspreyVar, ids[3]).belief > 0.0 &&
          fabs(g_array_index(ctx->graph->vars, OspreyVar, ids[3]).belief /
               DBL_MIN - 1.0) < 1e-12,
          "DBL_MIN prior remains representable in log space");
    CHECK(g_array_index(ctx->graph->vars, OspreyVar, ids[4]).belief ==
              probabilities[4],
          "prior adjacent to one remains distinguishable from hard support");
    for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) {
        CHECK(g_array_index(ctx->graph->vars, OspreyVar, ids[i]).belief_valid == 1,
              "exact endpoint and finite marginals retain validity");
    }
    osprey_free(ctx);
}

static void test_exact_log_domain_chain(void)
{
    OspreyConfig config = graph_config();
    OspreyContext *ctx;
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t ids[64];

    config.max_exact_clique_vars = 2;
    ctx = new_graph_context_with_config(&config);
    for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) {
        ids[i] = add_primitive(ctx, region, (int64_t)i * 8);
        add_prior_probability(ctx, OSPREY_RULE_CA01,
                              OSPREY_GRAPH_BASE_CA, 0.5, ids[i]);
        if (i != 0) {
            add_implication_probability(ctx, OSPREY_RULE_CA02,
                                        OSPREY_GRAPH_BASE_CA, false, DBL_MIN,
                                        &ids[i - 1], 1, ids[i]);
        }
    }
    CHECK(osprey_stage4_exact(ctx) == OSPREY_OK,
          "log-domain chain avoids ordinary-domain joint underflow");
    for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) {
        double belief = g_array_index(ctx->graph->vars, OspreyVar,
                                      ids[i]).belief;
        CHECK(isfinite(belief) && belief >= 0.0 && belief <= 1.0,
              "underflow-resistant chain publishes finite marginals");
    }
    osprey_free(ctx);
}

static void test_exact_separator_marginals(void)
{
    typedef struct TestEdge {
        unsigned source;
        unsigned target;
        double probability;
        uint16_t rule;
        bool negative;
    } TestEdge;
    OspreyConfig config = graph_config();
    OspreyContext *ctx;
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t ids[4];
    const double priors[4] = { 0.2, 0.3, 0.4, 0.6 };
    const TestEdge edges[] = {
        { 0, 1, 0.7, OSPREY_RULE_CA02, false },
        { 0, 2, 0.2, OSPREY_RULE_CA03, true },
        { 1, 2, 0.6, OSPREY_RULE_CA02, false },
        { 0, 3, 0.5, OSPREY_RULE_CA02, false },
        { 1, 3, 0.9, OSPREY_RULE_CA02, false },
    };
    double weights[1u << G_N_ELEMENTS(ids)] = { 0.0 };
    double expected[4] = { 0.0 };
    double partition = 0.0;

    config.max_exact_clique_vars = 3;
    ctx = new_graph_context_with_config(&config);
    for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) {
        ids[i] = add_primitive(ctx, region, (int64_t)i * 8);
        add_prior_probability(ctx, OSPREY_RULE_CA01,
                              OSPREY_GRAPH_BASE_CA, priors[i], ids[i]);
    }
    for (unsigned i = 0; i < G_N_ELEMENTS(edges); i++) {
        const TestEdge *edge = &edges[i];
        add_implication_probability(ctx, edge->rule,
                                    OSPREY_GRAPH_BASE_CA, edge->negative,
                                    edge->probability, &ids[edge->source], 1,
                                    ids[edge->target]);
    }
    for (unsigned assignment = 0; assignment < G_N_ELEMENTS(weights);
         assignment++) {
        double weight = 1.0;
        for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) {
            weight *= ((assignment >> i) & 1u) != 0 ? priors[i] :
                                                      1.0 - priors[i];
        }
        for (unsigned i = 0; i < G_N_ELEMENTS(edges); i++) {
            const TestEdge *edge = &edges[i];
            bool source = ((assignment >> edge->source) & 1u) != 0;
            bool target = ((assignment >> edge->target) & 1u) != 0;
            if (source) {
                weight *= target ? edge->probability :
                                    1.0 - edge->probability;
            } else {
                weight *= fmax(edge->probability,
                               1.0 - edge->probability);
            }
        }
        weights[assignment] = weight;
        partition += weight;
        for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) {
            if (((assignment >> i) & 1u) != 0) expected[i] += weight;
        }
    }
    for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) expected[i] /= partition;

    CHECK(osprey_stage4_exact(ctx) == OSPREY_OK,
          "exact inference handles a two-variable separator");
    for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) {
        CHECK(fabs(g_array_index(ctx->graph->vars, OspreyVar, ids[i]).belief -
                   expected[i]) < 1e-12,
              "multi-clique marginal matches brute-force enumeration");
    }
    osprey_free(ctx);
}

static void test_exact_bidirectional(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t a = add_primitive(ctx, region, 0);
    uint32_t b = add_primitive(ctx, region, 8);
    const double p_a = 0.35;
    const double p_b = 0.65;
    const double p_edge = 0.2;
    const double neutral = 1.0 - p_edge;
    double weights[4];
    double partition;
    double expected_a;
    double expected_b;

    add_prior_probability(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                          p_a, a);
    add_prior_probability(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                          p_b, b);
    OspreyFactorBatchResult batch = osprey_factor_add_bidirectional(
        ctx, OSPREY_RULE_CA03, OSPREY_GRAPH_BASE_CA, true, p_edge, a, b);
    CHECK(batch.status == OSPREY_OK && batch.inserted == 2,
          "bidirectional negative factors inserted");

    weights[0] = (1.0 - p_a) * (1.0 - p_b) * neutral * neutral;
    weights[1] = p_a * (1.0 - p_b) * neutral * neutral;
    weights[2] = (1.0 - p_a) * p_b * neutral * neutral;
    weights[3] = p_a * p_b * p_edge * p_edge;
    partition = weights[0] + weights[1] + weights[2] + weights[3];
    expected_a = (weights[1] + weights[3]) / partition;
    expected_b = (weights[2] + weights[3]) / partition;

    CHECK(osprey_stage4_exact(ctx) == OSPREY_OK,
          "bidirectional exact inference succeeds");
    CHECK(fabs(g_array_index(ctx->graph->vars, OspreyVar, a).belief -
               expected_a) < 1e-12 &&
          fabs(g_array_index(ctx->graph->vars, OspreyVar, b).belief -
               expected_b) < 1e-12,
          "both directions match the exact joint distribution");
    osprey_free(ctx);
}

#define REFERENCE_MAX_FACTORS 64u

typedef struct ReferenceFixture {
    Stage4ReferenceVariable variables[STAGE4_REFERENCE_MAX_VARS];
    uint32_t variable_count;
    Stage4ReferenceFactor factors[REFERENCE_MAX_FACTORS];
    uint32_t factor_count;
} ReferenceFixture;

static uint32_t reference_add_variable(ReferenceFixture *fixture,
                                       uint8_t kind,
                                       OspreyRegionId region,
                                       int64_t offset, uint64_t pc)
{
    uint32_t index;
    Stage4ReferenceVariable *variable;

    if (fixture == NULL || fixture->variable_count >=
            STAGE4_REFERENCE_MAX_VARS) {
        CHECK(false, "reference variable capacity is sufficient");
        return UINT32_MAX;
    }
    index = fixture->variable_count++;
    variable = &fixture->variables[index];
    memset(variable, 0, sizeof(*variable));
    variable->kind = kind;
    switch (kind) {
    case OSPREY_PRED_PRIMITIVE_VAR:
    case OSPREY_PRED_SCALAR:
        variable->payload.chunk = make_chunk(region, offset, 8);
        break;
    case OSPREY_PRED_PRIMITIVE_ACCESS:
        variable->payload.prim_access.chunk = make_chunk(region, offset, 8);
        variable->payload.prim_access.insn_pc = pc;
        break;
    default:
        CHECK(false, "reference variable kind has a complete fixture helper");
        break;
    }
    return index;
}

static uint32_t reference_add_field(ReferenceFixture *fixture,
                                    OspreyRegionId region, int64_t offset,
                                    OspreyAddress base)
{
    uint32_t index;
    Stage4ReferenceVariable *variable;

    if (fixture == NULL || fixture->variable_count >=
            STAGE4_REFERENCE_MAX_VARS) {
        CHECK(false, "reference field capacity is sufficient");
        return UINT32_MAX;
    }
    index = fixture->variable_count++;
    variable = &fixture->variables[index];
    memset(variable, 0, sizeof(*variable));
    variable->kind = OSPREY_PRED_FIELD_OF;
    variable->payload.attached.chunk = make_chunk(region, offset, 8);
    variable->payload.attached.base = base;
    return index;
}

static bool reference_add_prior(ReferenceFixture *fixture, uint16_t rule,
                                double probability, uint32_t variable)
{
    Stage4ReferenceFactor *factor;

    if (fixture == NULL || fixture->factor_count >= REFERENCE_MAX_FACTORS ||
        variable >= fixture->variable_count) {
        CHECK(false, "reference factor capacity is sufficient");
        return false;
    }
    factor = &fixture->factors[fixture->factor_count++];
    memset(factor, 0, sizeof(*factor));
    factor->rule = rule;
    factor->stage = OSPREY_GRAPH_BASE_CA;
    factor->potential_kind = OSPREY_POTENTIAL_PRIOR;
    factor->head_idx = 0;
    factor->probability = probability;
    factor->num_vars = 1;
    factor->vars[0] = variable;
    return true;
}

static bool reference_add_edge(ReferenceFixture *fixture, uint16_t rule,
                               bool negative, double probability,
                               uint32_t source, uint32_t target)
{
    Stage4ReferenceFactor *factor;

    if (fixture == NULL || fixture->factor_count >= REFERENCE_MAX_FACTORS ||
        source >= fixture->variable_count || target >= fixture->variable_count ||
        source == target) {
        CHECK(false, "reference edge has valid variables");
        return false;
    }
    factor = &fixture->factors[fixture->factor_count++];
    memset(factor, 0, sizeof(*factor));
    factor->rule = rule;
    factor->stage = OSPREY_GRAPH_BASE_CA;
    factor->potential_kind = OSPREY_POTENTIAL_IMPLICATION;
    factor->head_idx = 1;
    factor->negative = negative ? 1 : 0;
    factor->probability = probability;
    factor->num_vars = 2;
    factor->vars[0] = source;
    factor->vars[1] = target;
    return true;
}

static OspreyContext *reference_build_context(
    const ReferenceFixture *fixture, const uint32_t *variable_order,
    const uint32_t *factor_order, uint32_t duplicate_factor,
    uint32_t *production_ids)
{
    OspreyContext *ctx;
    OspreyConfig config = graph_config();

    if (fixture == NULL || production_ids == NULL) return NULL;
    ctx = new_graph_context_with_config(&config);
    for (uint32_t i = 0; i < fixture->variable_count; i++) {
        uint32_t index = variable_order == NULL ? i : variable_order[i];
        OspreyInternResult result;
        if (index >= fixture->variable_count) {
            CHECK(false, "reference variable insertion order is valid");
            osprey_free(ctx);
            return NULL;
        }
        result = osprey_intern_var(ctx, fixture->variables[index].kind,
                                   &fixture->variables[index].payload);
        CHECK(result.id != UINT32_MAX, "reference variable inserts");
        if (result.id == UINT32_MAX) {
            osprey_free(ctx);
            return NULL;
        }
        production_ids[index] = result.id;
    }
    for (uint32_t i = 0; i < fixture->factor_count; i++) {
        uint32_t index = factor_order == NULL ? i : factor_order[i];
        const Stage4ReferenceFactor *spec;
        uint32_t ids[OSPREY_FACTOR_MAX_ARITY];
        OspreyFactorResult result;

        if (index >= fixture->factor_count) {
            CHECK(false, "reference factor insertion order is valid");
            osprey_free(ctx);
            return NULL;
        }
        spec = &fixture->factors[index];
        for (uint32_t j = 0; j < spec->num_vars; j++) {
            if (spec->vars[j] >= fixture->variable_count) {
                CHECK(false, "reference factor variables are valid");
                osprey_free(ctx);
                return NULL;
            }
            ids[j] = production_ids[spec->vars[j]];
        }
        result = osprey_factor_add_ex(
            ctx, spec->rule, spec->stage, spec->potential_kind,
            spec->head_idx, spec->negative != 0, spec->probability, ids,
            spec->num_vars);
        CHECK(result.status == OSPREY_OK && result.id != UINT32_MAX,
              "reference factor inserts");
        if (result.status != OSPREY_OK || result.id == UINT32_MAX) {
            osprey_free(ctx);
            return NULL;
        }
        if (index == duplicate_factor) {
            OspreyFactorResult duplicate = osprey_factor_add_ex(
                ctx, spec->rule, spec->stage, spec->potential_kind,
                spec->head_idx, spec->negative != 0, spec->probability, ids,
                spec->num_vars);
            CHECK(duplicate.status == OSPREY_OK && !duplicate.inserted,
                  "duplicate reference factor is ignored");
            if (duplicate.status != OSPREY_OK || duplicate.inserted) {
                osprey_free(ctx);
                return NULL;
            }
        }
    }
    return ctx;
}

static bool reference_results_match(const ReferenceFixture *fixture,
                                    const OspreyContext *ctx,
                                    const Stage4ReferenceSolution *solution)
{
    bool matched[STAGE4_REFERENCE_MAX_VARS] = { false };
    bool ok = true;

    if (fixture == NULL || ctx == NULL || ctx->graph == NULL ||
        solution == NULL || ctx->graph->vars == NULL ||
        ctx->graph->vars->len != fixture->variable_count ||
        ctx->graph->factors == NULL ||
        ctx->graph->factors->len != fixture->factor_count) {
        CHECK(false, "production graph has exactly the declarative shape");
        return false;
    }
    for (guint graph_id = 0; graph_id < ctx->graph->vars->len; graph_id++) {
        const OspreyVar *actual = &g_array_index(ctx->graph->vars,
                                                  OspreyVar, graph_id);
        OspreyKey actual_key = osprey_var_key(actual->kind, &actual->payload);
        uint32_t expected_id = UINT32_MAX;
        for (uint32_t i = 0; i < fixture->variable_count; i++) {
            OspreyKey expected_key = osprey_var_key(
                fixture->variables[i].kind, &fixture->variables[i].payload);
            if (osprey_key_equal(&actual_key, &expected_key)) {
                if (expected_id != UINT32_MAX) {
                    CHECK(false, "production variable keys are unique");
                    ok = false;
                }
                expected_id = i;
            }
        }
        if (expected_id == UINT32_MAX || matched[expected_id]) {
            CHECK(false, "production variable maps by its complete key");
            ok = false;
            continue;
        }
        matched[expected_id] = true;
        CHECK(isfinite(actual->belief) && actual->belief >= 0.0 &&
                  actual->belief <= 1.0,
              "production marginal is normalized");
        CHECK(fabs(actual->belief - solution->marginals[expected_id]) <= 1e-10,
              "production marginal matches independent brute force");
        if (!isfinite(actual->belief) || actual->belief < 0.0 ||
            actual->belief > 1.0 ||
            fabs(actual->belief - solution->marginals[expected_id]) > 1e-10) {
            ok = false;
        }
    }
    for (uint32_t i = 0; i < fixture->variable_count; i++) {
        if (!matched[i]) {
            CHECK(false, "every declarative variable receives one marginal");
            ok = false;
        }
    }
    {
        double scale = fmax(1.0, fmax(fabs(ctx->last_exact_logz),
                                     fabs(solution->logz)));
        double difference = fabs(ctx->last_exact_logz - solution->logz);
        CHECK(isfinite(ctx->last_exact_logz) &&
                  difference <= 1e-10 * scale,
              "production log partition matches independent brute force");
        if (!isfinite(ctx->last_exact_logz) || difference > 1e-10 * scale) {
            ok = false;
        }
    }
    return ok;
}

static bool reference_run_fixture(const ReferenceFixture *fixture,
                                  const uint32_t *variable_order,
                                  const uint32_t *factor_order,
                                  uint32_t duplicate_factor)
{
    Stage4ReferenceProblem problem;
    Stage4ReferenceSolution solution;
    uint32_t production_ids[STAGE4_REFERENCE_MAX_VARS] = { 0 };
    OspreyContext *ctx;
    OspreyExactBase *base = NULL;
    OspreyExactTopology *topology = NULL;
    OspreyStatus reference_status;
    OspreyStatus status;
    double beliefs_before[STAGE4_REFERENCE_MAX_VARS];
    bool ok = true;

    memset(&problem, 0, sizeof(problem));
    problem.variables = fixture->variables;
    problem.variable_count = fixture->variable_count;
    problem.factors = fixture->factors;
    problem.factor_count = fixture->factor_count;
    reference_status = stage4_exact_reference_bruteforce(&problem, &solution);
    CHECK(reference_status == OSPREY_OK ||
              reference_status == OSPREY_INVALID_MODEL,
          "declarative reference graph has a valid exact status");
    if (reference_status != OSPREY_OK &&
        reference_status != OSPREY_INVALID_MODEL) return false;

    ctx = reference_build_context(fixture, variable_order, factor_order,
                                  duplicate_factor, production_ids);
    if (ctx == NULL) return false;
    for (guint i = 0; i < ctx->graph->vars->len; i++) {
        beliefs_before[i] = g_array_index(ctx->graph->vars, OspreyVar,
                                           i).belief;
    }
    status = build_test_topology(ctx, &base, &topology);
    CHECK(status == OSPREY_OK && base != NULL && topology != NULL,
          "production exact topology accepts declarative graph");
    if (status != OSPREY_OK || base == NULL || topology == NULL) {
        ok = false;
        goto out;
    }
    CHECK(base->graph_var_ids->len == fixture->variable_count &&
              base->factor_refs->len == fixture->factor_count,
          "exact projection solves only registered base variables/factors");
    bool topology_matches = stage4_exact_reference_validate(base, topology);
    CHECK(topology_matches,
          "generated topology agrees with independent bounded topology oracle");
    if (base->graph_var_ids->len != fixture->variable_count ||
        base->factor_refs->len != fixture->factor_count || !topology_matches) {
        ok = false;
    }
    status = osprey_stage4_exact(ctx);
    CHECK(status == reference_status,
          "production exact status matches independent brute force");
    if (status != reference_status) {
        ok = false;
    } else if (reference_status == OSPREY_OK) {
        if (!reference_results_match(fixture, ctx, &solution)) ok = false;
    } else {
        for (guint i = 0; i < ctx->graph->vars->len; i++) {
            if (g_array_index(ctx->graph->vars, OspreyVar, i).belief !=
                beliefs_before[i]) {
                CHECK(false, "impossible generated model publishes no belief");
                ok = false;
            }
        }
        CHECK(isnan(ctx->last_exact_logz),
              "impossible generated model publishes no partition");
        if (!isnan(ctx->last_exact_logz)) ok = false;
    }
out:
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    osprey_free(ctx);
    return ok;
}

static void test_reference_generic_factors(void)
{
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyRegionId stack = make_region(OSPREY_REGION_STACK_FUNCTION, 0x100);
    ReferenceFixture fixture;
    OspreyAddress field_base;
    uint32_t first;
    uint32_t second;

    memset(&fixture, 0, sizeof(fixture));
    first = reference_add_variable(&fixture, OSPREY_PRED_PRIMITIVE_VAR,
                                   global, 0, 0);
    reference_add_prior(&fixture, OSPREY_RULE_CA01, 0.6, first);
    CHECK(reference_run_fixture(&fixture, NULL, NULL, UINT32_MAX),
          "CA01 reference case matches brute force");

    memset(&fixture, 0, sizeof(fixture));
    first = reference_add_variable(&fixture, OSPREY_PRED_PRIMITIVE_VAR,
                                   global, 0, 0);
    second = reference_add_variable(&fixture, OSPREY_PRED_PRIMITIVE_VAR,
                                    global, 8, 0);
    reference_add_prior(&fixture, OSPREY_RULE_CA01, 0.3, first);
    reference_add_prior(&fixture, OSPREY_RULE_CA01, 0.7, second);
    reference_add_edge(&fixture, OSPREY_RULE_CA02, false, 0.8, first, second);
    CHECK(reference_run_fixture(&fixture, NULL, NULL, 2),
          "CA02 reference case matches brute force");

    reference_add_edge(&fixture, OSPREY_RULE_CA02, false, 0.8, second, first);
    CHECK(reference_run_fixture(&fixture, NULL, NULL, UINT32_MAX),
          "CA02 bidirectional reference case matches brute force");

    memset(&fixture, 0, sizeof(fixture));
    first = reference_add_variable(&fixture, OSPREY_PRED_PRIMITIVE_VAR,
                                   global, 0, 0);
    second = reference_add_variable(&fixture, OSPREY_PRED_PRIMITIVE_VAR,
                                    global, 8, 0);
    reference_add_prior(&fixture, OSPREY_RULE_CA01, 0.3, first);
    reference_add_prior(&fixture, OSPREY_RULE_CA01, 0.7, second);
    reference_add_edge(&fixture, OSPREY_RULE_CA03, true, 0.2, first, second);
    CHECK(reference_run_fixture(&fixture, NULL, NULL, UINT32_MAX),
          "CA03 reference case matches brute force");

    reference_add_edge(&fixture, OSPREY_RULE_CA03, true, 0.2, second, first);
    CHECK(reference_run_fixture(&fixture, NULL, NULL, UINT32_MAX),
          "CA03 bidirectional reference case matches brute force");

    memset(&fixture, 0, sizeof(fixture));
    first = reference_add_variable(&fixture, OSPREY_PRED_PRIMITIVE_VAR,
                                   global, 0, 0);
    second = reference_add_variable(&fixture, OSPREY_PRED_PRIMITIVE_ACCESS,
                                    stack, -8, 0x10);
    reference_add_prior(&fixture, OSPREY_RULE_CA01, 0.4, first);
    reference_add_edge(&fixture, OSPREY_RULE_CA04, false, 0.8, first, second);
    CHECK(reference_run_fixture(&fixture, NULL, NULL, UINT32_MAX),
          "CA04 reference case matches brute force");

    memset(&fixture, 0, sizeof(fixture));
    first = reference_add_variable(&fixture, OSPREY_PRED_PRIMITIVE_ACCESS,
                                   stack, -8, 0x11);
    second = reference_add_variable(&fixture, OSPREY_PRED_PRIMITIVE_VAR,
                                    global, 8, 0);
    reference_add_prior(&fixture, OSPREY_RULE_CA01, 0.6, second);
    reference_add_edge(&fixture, OSPREY_RULE_CA05, false, 0.8, first, second);
    CHECK(reference_run_fixture(&fixture, NULL, NULL, UINT32_MAX),
          "CA05 reference case matches brute force");

    memset(&fixture, 0, sizeof(fixture));
    first = reference_add_variable(&fixture, OSPREY_PRED_PRIMITIVE_ACCESS,
                                   stack, -8, 0x12);
    second = reference_add_variable(&fixture, OSPREY_PRED_SCALAR,
                                    global, 16, 0);
    reference_add_edge(&fixture, OSPREY_RULE_CA06, false, 0.5, first, second);
    CHECK(reference_run_fixture(&fixture, NULL, NULL, UINT32_MAX),
          "CA06 reference case matches brute force");

    memset(&fixture, 0, sizeof(fixture));
    first = reference_add_variable(&fixture, OSPREY_PRED_SCALAR,
                                   global, 0, 0);
    second = reference_add_variable(&fixture, OSPREY_PRED_SCALAR,
                                    global, 8, 0);
    reference_add_edge(&fixture, OSPREY_RULE_CA07, false, 0.2, first, second);
    CHECK(reference_run_fixture(&fixture, NULL, NULL, UINT32_MAX),
          "CA07 lower-clamp reference case matches brute force");

    memset(&fixture, 0, sizeof(fixture));
    first = reference_add_variable(&fixture, OSPREY_PRED_SCALAR,
                                   global, 0, 0);
    second = reference_add_variable(&fixture, OSPREY_PRED_SCALAR,
                                    global, 8, 0);
    reference_add_edge(&fixture, OSPREY_RULE_CA07, false, 0.8, first, second);
    CHECK(reference_run_fixture(&fixture, NULL, NULL, UINT32_MAX),
          "CA07 upper-clamp reference case matches brute force");

    memset(&fixture, 0, sizeof(fixture));
    first = reference_add_variable(&fixture, OSPREY_PRED_SCALAR,
                                   global, 0, 0);
    field_base = (OspreyAddress) { global, 0 };
    second = reference_add_field(&fixture, global, 0, field_base);
    reference_add_edge(&fixture, OSPREY_RULE_CA08, true, 0.2, first, second);
    CHECK(reference_run_fixture(&fixture, NULL, NULL, UINT32_MAX),
          "CA08 reference case matches brute force");
    reference_add_edge(&fixture, OSPREY_RULE_CA08, true, 0.2, second, first);
    CHECK(reference_run_fixture(&fixture, NULL, NULL, UINT32_MAX),
          "late CA08 bidirectional case matches brute force");
}

static uint64_t reference_rng_next(uint64_t *state)
{
    *state = *state * UINT64_C(6364136223846793005) +
             UINT64_C(1442695040888963407);
    return *state;
}

static double reference_generated_probability(uint64_t *state, bool prior)
{
    static const double edge_values[] = {
        0.0, 1.0, 0.2, 0.5, 0.8, DBL_MIN,
    };
    static const double prior_values[] = {
        0.0, 1.0, 0.2, 0.5, 0.8, DBL_MIN,
    };
    const double *values = prior ? prior_values : edge_values;
    size_t count = prior ? G_N_ELEMENTS(prior_values) :
                          G_N_ELEMENTS(edge_values);
    double value = values[reference_rng_next(state) % count];

    if (!prior && (reference_rng_next(state) & 7u) == 0) {
        value = nextafter(1.0, 0.0);
    }
    return value;
}

static void reference_shuffle(uint32_t *values, uint32_t count,
                              uint64_t *state)
{
    if (values == NULL || state == NULL) return;
    for (uint32_t i = count; i > 1; i--) {
        uint32_t j = reference_rng_next(state) % i;
        uint32_t temporary = values[i - 1];
        values[i - 1] = values[j];
        values[j] = temporary;
    }
}

static void reference_generated_edge(ReferenceFixture *fixture,
                                     uint64_t *state, uint32_t source,
                                     uint32_t target)
{
    bool negative = (reference_rng_next(state) & 1u) != 0;
    reference_add_edge(fixture,
                       negative ? OSPREY_RULE_CA03 : OSPREY_RULE_CA02,
                       negative, reference_generated_probability(state, false),
                       source, target);
}

static void reference_generate_fixture(uint32_t seed,
                                        ReferenceFixture *fixture,
                                        uint64_t *state_out)
{
    uint64_t state = UINT64_C(0x9e3779b97f4a7c15) ^ seed;
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, seed & 3u);
    OspreyRegionId stack = make_region(OSPREY_REGION_STACK_FUNCTION,
                                       0x100 + (seed & 1u) * 0x100);
    uint32_t shape;

    memset(fixture, 0, sizeof(*fixture));
    uint32_t variable_count = 1 + reference_rng_next(&state) %
                                    STAGE4_REFERENCE_MAX_VARS;
    bool add_ca05 = variable_count >= 2 && (seed & 7u) == 0;
    uint32_t primitive_first = add_ca05 ? 1 : 0;
    uint32_t primitive_count = variable_count - primitive_first;
    for (uint32_t i = 0; i < variable_count; i++) {
        OspreyRegionId region = (i & 1u) == 0 ? global : stack;
        int64_t offset = (i & 1u) == 0
            ? (int64_t)i * 8
            : -((int64_t)i + 1) * 8;
        uint8_t kind = add_ca05 && i == 0
            ? OSPREY_PRED_PRIMITIVE_ACCESS
            : OSPREY_PRED_PRIMITIVE_VAR;
        uint32_t id = reference_add_variable(
            fixture, kind, region, offset, UINT64_C(0x1000) + seed);
        if (kind == OSPREY_PRED_PRIMITIVE_VAR) {
            reference_add_prior(
                fixture, OSPREY_RULE_CA01,
                reference_generated_probability(&state, true), id);
        }
    }
    if (add_ca05) {
        reference_add_edge(
            fixture, OSPREY_RULE_CA05, false,
            reference_generated_probability(&state, false), 0, 1);
    }

    shape = reference_rng_next(&state) % 4;
    if (shape == 1 && primitive_count >= 3 && primitive_count <= 6) {
        for (uint32_t i = 0; i < primitive_count; i++) {
            reference_generated_edge(
                fixture, &state, primitive_first + i,
                primitive_first + (i + 1) % primitive_count);
        }
    } else if (shape == 2 && primitive_count <= 6) {
        for (uint32_t i = 1; i < primitive_count; i++) {
            reference_generated_edge(fixture, &state,
                                     primitive_first + i, primitive_first);
        }
    } else if (shape == 3) {
        for (uint32_t i = 0; i + 1 < primitive_count; i += 2) {
            reference_generated_edge(fixture, &state, primitive_first + i,
                                     primitive_first + i + 1);
        }
    } else {
        for (uint32_t i = 1; i < primitive_count; i++) {
            reference_generated_edge(fixture, &state,
                                     primitive_first + i - 1,
                                     primitive_first + i);
        }
    }
    if (state_out != NULL) *state_out = state;
}

static void reference_dump_generated_fixture(
    uint32_t seed, const ReferenceFixture *fixture)
{
    fprintf(stderr, "generated Stage-4 reference seed %u: vars %u factors %u\n",
            seed, fixture->variable_count, fixture->factor_count);
    for (uint32_t i = 0; i < fixture->variable_count; i++) {
        const Stage4ReferenceVariable *variable = &fixture->variables[i];
        OspreyKey key = osprey_var_key(variable->kind, &variable->payload);
        fprintf(stderr, "  V %u kind %u key", i, variable->kind);
        for (guint word = 0; word < G_N_ELEMENTS(key.w); word++) {
            fprintf(stderr, " %016llx",
                    (unsigned long long)key.w[word]);
        }
        fputc('\n', stderr);
    }
    for (uint32_t i = 0; i < fixture->factor_count; i++) {
        const Stage4ReferenceFactor *factor = &fixture->factors[i];
        uint64_t probability_bits;
        memcpy(&probability_bits, &factor->probability,
               sizeof(probability_bits));
        fprintf(stderr,
                "  F %u rule %u stage %u potential %u negative %u "
                "p %016llx head %u arity %u vars",
                i, factor->rule, factor->stage, factor->potential_kind,
                factor->negative, (unsigned long long)probability_bits,
                factor->head_idx, factor->num_vars);
        for (uint32_t j = 0; j < factor->num_vars; j++) {
            fprintf(stderr, " %u", factor->vars[j]);
        }
        fputc('\n', stderr);
    }
}

static bool run_generated_reference_case(uint32_t seed)
{
    ReferenceFixture fixture;
    uint32_t natural_variables[STAGE4_REFERENCE_MAX_VARS];
    uint32_t natural_factors[REFERENCE_MAX_FACTORS];
    uint32_t shuffled_variables[STAGE4_REFERENCE_MAX_VARS];
    uint32_t shuffled_factors[REFERENCE_MAX_FACTORS];
    uint64_t state;
    uint32_t duplicate;
    bool first;
    bool second;

    reference_generate_fixture(seed, &fixture, &state);
    for (uint32_t i = 0; i < fixture.variable_count; i++) {
        natural_variables[i] = i;
        shuffled_variables[i] = i;
    }
    for (uint32_t i = 0; i < fixture.factor_count; i++) {
        natural_factors[i] = i;
        shuffled_factors[i] = i;
    }
    reference_shuffle(shuffled_variables, fixture.variable_count, &state);
    reference_shuffle(shuffled_factors, fixture.factor_count, &state);
    duplicate = fixture.factor_count == 0 ? UINT32_MAX :
                (uint32_t)(seed % fixture.factor_count);
    first = reference_run_fixture(&fixture, natural_variables, natural_factors,
                                  UINT32_MAX);
    second = reference_run_fixture(&fixture, shuffled_variables,
                                   shuffled_factors, duplicate);
    if (!first || !second) {
        reference_dump_generated_fixture(seed, &fixture);
    }
    return first && second;
}

static void test_generated_reference_corpus(void)
{
    enum { GENERATED_CASES = 2000 };

    for (uint32_t seed = 0; seed < GENERATED_CASES; seed++) {
        bool ok;
        generated_registered++;
        ok = run_generated_reference_case(UINT32_C(0x5eed0000) + seed);
        CHECK(ok, "generated Stage-4 seed matches the independent oracle");
        generated_executed++;
    }
    CHECK(generated_registered == GENERATED_CASES &&
              generated_executed == GENERATED_CASES,
          "every generated Stage-4 seed executes exactly once");
}

static void test_exact_allocation_failure(void)
{
    ReferenceFixture fixture;
    OspreyContext *ctx;
    uint32_t ids[STAGE4_REFERENCE_MAX_VARS] = { 0 };
    double first_before = 0.41;
    double second_before = 0.59;

    memset(&fixture, 0, sizeof(fixture));
    uint32_t first = reference_add_variable(
        &fixture, OSPREY_PRED_PRIMITIVE_VAR,
        make_region(OSPREY_REGION_GLOBAL, 0), 0, 0);
    uint32_t second = reference_add_variable(
        &fixture, OSPREY_PRED_PRIMITIVE_VAR,
        make_region(OSPREY_REGION_GLOBAL, 0), 8, 0);
    reference_add_prior(&fixture, OSPREY_RULE_CA01, 0.4, first);
    reference_add_prior(&fixture, OSPREY_RULE_CA01, 0.6, second);
    reference_add_edge(&fixture, OSPREY_RULE_CA02, false, 0.8,
                       first, second);
    ctx = reference_build_context(&fixture, NULL, NULL, UINT32_MAX, ids);
    CHECK(ctx != NULL, "allocation-failure fixture builds");
    if (ctx == NULL) return;
    g_array_index(ctx->graph->vars, OspreyVar, ids[first]).belief =
        first_before;
    g_array_index(ctx->graph->vars, OspreyVar, ids[second]).belief =
        second_before;
    osprey_exact_test_set_alloc_fail_after(1);
    OspreyStatus status = osprey_stage4_exact(ctx);
    osprey_exact_test_set_alloc_fail_after(-1);
    CHECK(status == OSPREY_INVALID_GRAPH,
          "deterministic numerical allocation failure rejects");
    CHECK(g_array_index(ctx->graph->vars, OspreyVar, ids[first]).belief ==
              first_before &&
          g_array_index(ctx->graph->vars, OspreyVar, ids[second]).belief ==
              second_before && isnan(ctx->last_exact_logz),
          "allocation failure publishes no beliefs or partition");
    osprey_free(ctx);
}

static void test_exact_repeated_invocation(void)
{
    ReferenceFixture fixture;
    OspreyContext *ctx;
    uint32_t ids[STAGE4_REFERENCE_MAX_VARS] = { 0 };
    double first_belief;
    double second_belief;
    double first_logz;
    double second_logz;
    OspreyFactor *factor;

    memset(&fixture, 0, sizeof(fixture));
    uint32_t first = reference_add_variable(
        &fixture, OSPREY_PRED_PRIMITIVE_VAR,
        make_region(OSPREY_REGION_GLOBAL, 0), 0, 0);
    uint32_t second = reference_add_variable(
        &fixture, OSPREY_PRED_PRIMITIVE_VAR,
        make_region(OSPREY_REGION_GLOBAL, 0), 8, 0);
    reference_add_prior(&fixture, OSPREY_RULE_CA01, 0.35, first);
    reference_add_prior(&fixture, OSPREY_RULE_CA01, 0.65, second);
    reference_add_edge(&fixture, OSPREY_RULE_CA02, false, 0.8,
                       first, second);

    ctx = reference_build_context(&fixture, NULL, NULL, UINT32_MAX, ids);
    CHECK(ctx != NULL, "repeated exact fixture builds");
    if (ctx == NULL) return;
    CHECK(osprey_stage4_exact(ctx) == OSPREY_OK,
          "first exact invocation succeeds");
    first_belief = g_array_index(ctx->graph->vars, OspreyVar, ids[first]).belief;
    second_belief = g_array_index(ctx->graph->vars, OspreyVar, ids[second]).belief;
    first_logz = ctx->last_exact_logz;
    CHECK(osprey_stage4_exact(ctx) == OSPREY_OK,
          "second exact invocation succeeds");
    CHECK(g_array_index(ctx->graph->vars, OspreyVar, ids[first]).belief ==
              first_belief &&
          g_array_index(ctx->graph->vars, OspreyVar, ids[second]).belief ==
              second_belief && ctx->last_exact_logz == first_logz,
          "repeated success is deterministic");

    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 0);
    factor->p = NAN;
    first_belief = g_array_index(ctx->graph->vars, OspreyVar, ids[first]).belief;
    second_belief = g_array_index(ctx->graph->vars, OspreyVar, ids[second]).belief;
    first_logz = ctx->last_exact_logz;
    CHECK(osprey_stage4_exact(ctx) == OSPREY_INVALID_GRAPH,
          "malformed repeated exact invocation rejects");
    CHECK(g_array_index(ctx->graph->vars, OspreyVar, ids[first]).belief ==
              first_belief &&
          g_array_index(ctx->graph->vars, OspreyVar, ids[second]).belief ==
              second_belief && ctx->last_exact_logz == first_logz,
          "repeated rejection preserves committed exact result");
    factor->p = INFINITY;
    CHECK(osprey_stage4_exact(ctx) == OSPREY_INVALID_GRAPH,
          "positive-infinity factor rejects atomically");
    CHECK(g_array_index(ctx->graph->vars, OspreyVar, ids[first]).belief ==
              first_belief &&
          g_array_index(ctx->graph->vars, OspreyVar, ids[second]).belief ==
              second_belief && ctx->last_exact_logz == first_logz,
          "positive-infinity rejection preserves exact result");
    second_logz = ctx->last_exact_logz;
    CHECK(second_logz == first_logz, "rejection leaves exact log partition intact");
    osprey_free(ctx);
}

static void test_exact_atomic_failure(void)
{
    OspreyContext *ctx = new_graph_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t first = add_primitive(ctx, region, 0);
    uint32_t contradictory = add_primitive(ctx, region, 8);
    double first_before = 0.31;
    double contradictory_before = 0.62;

    add_prior_probability(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                          0.8, first);
    add_prior_probability(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                          0.0, contradictory);
    add_prior_probability(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                          1.0, contradictory);
    g_array_index(ctx->graph->vars, OspreyVar, first).belief = first_before;
    g_array_index(ctx->graph->vars, OspreyVar,
                  contradictory).belief = contradictory_before;

    CHECK(osprey_stage4_exact(ctx) == OSPREY_INVALID_MODEL,
          "contradictory exact component rejects as an invalid model");
    CHECK(g_array_index(ctx->graph->vars, OspreyVar, first).belief ==
              first_before &&
          g_array_index(ctx->graph->vars, OspreyVar,
                        contradictory).belief == contradictory_before,
          "failed exact inference publishes no partial marginals");
    osprey_free(ctx);
}

int main(void)
{
    RUN(test_stage_selection);
    RUN(test_late_ca08);
    RUN(test_secondary_contamination);
    RUN(test_ca05_bridge);
    RUN(test_unary_components);
    RUN(test_complete_map_initialization);
    RUN(test_accepted_predicate_order);
    RUN(test_insertion_permutations);
    RUN(test_malformed_graphs);
    RUN(test_empty_base);
    RUN(test_repeated_ownership);
    RUN(test_chain_width_and_order);
    RUN(test_width_boundaries);
    RUN(test_width_four_clique);
    RUN(test_star_and_unary_topology);
    RUN(test_reference_topology_oracle);
    RUN(test_cross_region_and_late_topology);
    RUN(test_topology_determinism_and_validator);
    RUN(test_exact_configuration);
    RUN(test_workspace_budget);
    RUN(test_exact_log_arithmetic);
    RUN(test_exact_numeric_marginals);
    RUN(test_exact_extreme_support);
    RUN(test_exact_separator_marginals);
    RUN(test_exact_log_domain_chain);
    RUN(test_exact_bidirectional);
    RUN(test_reference_generic_factors);
    RUN(test_generated_reference_corpus);
    RUN(test_exact_allocation_failure);
    RUN(test_exact_repeated_invocation);
    RUN(test_exact_atomic_failure);
    CHECK(registered == executed, "every Stage 4 exact case executed");
    CHECK(generated_registered == 2000 && generated_executed == 2000,
          "all generated Stage-4 cases report exact totals");
    if (failures != 0 || registered != executed ||
        generated_registered != 2000 || generated_executed != 2000) {
        fprintf(stderr, "FAIL stage4_exact (%u failures, %u/%u; generated %u/%u)\n",
                failures, executed, registered, generated_executed,
                generated_registered);
        return 1;
    }
    printf("PASS stage4_exact (%u/%u; generated %u/%u)\n", executed,
           registered, generated_executed, generated_registered);
    return 0;
}
