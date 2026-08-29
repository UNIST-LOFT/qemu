/* Stage 4.1 CA-only projection and component-boundary tests. */

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

static OspreyContext *new_graph_context(void)
{
    OspreyConfig config = graph_config();
    OspreyContext *ctx = osprey_new(&config);
    ctx->graph = osprey_graph_new();
    return ctx;
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

static bool add_prior(OspreyContext *ctx, uint16_t rule, uint8_t stage,
                      uint32_t id)
{
    OspreyFactorResult result = osprey_factor_add_prior(
        ctx, rule, stage, false, 0.8, id);
    CHECK(result.status == OSPREY_OK, "prior factor inserted");
    return result.status == OSPREY_OK;
}

static bool add_implication(OspreyContext *ctx, uint16_t rule, uint8_t stage,
                            uint32_t source, uint32_t target)
{
    OspreyFactorResult result = osprey_factor_add_implication(
        ctx, rule, stage, false, 0.8, &source, 1, target);
    CHECK(result.status == OSPREY_OK, "implication factor inserted");
    return result.status == OSPREY_OK;
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
    CHECK(osprey_exact_base_build(ctx, &base) == OSPREY_OK,
          "permutation projection succeeds");
    char *dump = base == NULL ? g_strdup("") : projection_dump(ctx, base);
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
                      "projection canonical order ignores insertion order");
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
    for (unsigned mutation = 0; mutation < 9; mutation++) {
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
    CHECK(registered == executed, "every Stage 4.1 case executed");
    if (failures != 0 || registered != executed) {
        fprintf(stderr, "FAIL stage4_exact (%u failures, %u/%u)\n",
                failures, executed, registered);
        return 1;
    }
    printf("PASS stage4_exact (%u/%u)\n", executed, registered);
    return 0;
}
