/*
 * OSPREY deterministic closure (R01-R12), predicate interning, bounded
 * candidate generation, and static factor instantiation (Stage 2).
 *
 * Parent side only: runs after the baseline sample is merged.  This
 * stage delivers the abstract predicates and rule-instance factors the
 * inference stage solves; nothing here computes marginals.
 *
 * Rule semantics follow the corrected reference
 * (agent-docs/info/OSPREY_TYPE_INFERENCE/OSPREY_IMPLEMENTATION.md §4-§7):
 *  - R01-R09 deterministic aggregations over committed facts;
 *  - R10-R12 hint instances (DataFlow / UnifiedAccess / PointsTo);
 *  - CD04 closure extends HomoSegment candidates from hints;
 *  - factor convention (§7.1): compile A--p-->B as one factor that
 *    penalizes only the violated assignment by 1-p; split X<->Y into
 *    two directional factors; split multi-head consequents per head;
 *    p_k = min(1, distinct_sample_paths / total_sampled_paths) (§7.2);
 *    p_s = p_up scaled by normalized hint-instance support.
 *
 * Candidate discipline (§9):
 *  - addresses only from observed chunks, BaseAddr bases, region bases,
 *    heap bases, or rule endpoints;
 *  - arrays only from CB01-CB05 or canonical intervals, half-open hi,
 *    stride > 0, hi > lo, hi-lo >= s;
 *  - homo segments only from R10-R12 and CD04 closure, capped to
 *    observed region extent, starts aligned to observed chunk starts;
 *  - per-(kind,region) caps from config, with [osprey] [limit] rows.
 *
 * Determinism: all iterations are over insertion-ordered committed
 * GArrays (parent side), so the graph construction is reproducible.
 */

#include "osprey.h"
#include "osprey-internal.h"

/* Diagnostic sink (snapshot.c). */
void log_msg(const char *fmt, ...);

/* ------------------------------------------------------------------ */
/* Small helpers (H01-H06)                                             */
/* ------------------------------------------------------------------ */

static bool same_region(const OspreyRegionId *a, const OspreyRegionId *b) {
    return a->kind == b->kind && a->code_image_id == b->code_image_id &&
           a->site_offset == b->site_offset;
}

static bool same_region_addr(const OspreyAddress *a, const OspreyAddress *b) {
    return same_region(&a->region, &b->region);
}

/* H02: offset difference a-b; false when regions differ or overflow. */
static bool offset_between(const OspreyAddress *a, const OspreyAddress *b,
                           int64_t *out) {
    if (!same_region_addr(a, b)) return false;
    return osprey_check_sub(a->offset, b->offset, out);
}

static bool address_equal(const OspreyAddress *a, const OspreyAddress *b) {
    return same_region_addr(a, b) && a->offset == b->offset;
}

static bool chunk_equal(const OspreyChunk *a, const OspreyChunk *b) {
    return address_equal(&a->address, &b->address) && a->size == b->size;
}

static int64_t gcd_i64(int64_t a, int64_t b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static void insertion_sort_i64(GArray *a) {
    for (guint i = 1; i < a->len; i++) {
        int64_t v = g_array_index(a, int64_t, i);
        guint j = i;
        while (j > 0 && g_array_index(a, int64_t, j - 1) > v) {
            g_array_index(a, int64_t, j) = g_array_index(a, int64_t, j - 1);
            j--;
        }
        g_array_index(a, int64_t, j) = v;
    }
}

/* ------------------------------------------------------------------ */
/* Graph lifecycle                                                     */
/* ------------------------------------------------------------------ */

OspreyGraph *osprey_graph_new(void) {
    OspreyGraph *g = g_new0(OspreyGraph, 1);
    g->vars = g_array_new(FALSE, FALSE, sizeof(OspreyVar));
    g->var_index = g_hash_table_new_full(osprey_key_hash, osprey_key_equal,
                                         osprey_key_free, NULL);
    g->hints = g_array_new(FALSE, FALSE, sizeof(OspreyHint));
    g->factors = g_array_new(FALSE, FALSE, sizeof(OspreyFactor *));
    g->factor_index = g_hash_table_new_full(osprey_factor_key_hash,
                                            osprey_factor_key_equal,
                                            g_free, NULL);
    g->kind_region = g_hash_table_new_full(osprey_key_hash, osprey_key_equal,
                                           osprey_key_free, g_free);
    g->uf_parent = NULL;
    g->uf_size = 0;
    return g;
}

/* Free a factor graph and everything it owns (Stage 0/1 ownership). */
void osprey_graph_free(OspreyGraph *g) {
    if (g == NULL) return;
    if (g->factors != NULL) {
        for (guint i = 0; i < g->factors->len; i++) {
            OspreyFactor *f = g_array_index(g->factors, OspreyFactor *, i);
            if (f != NULL) {
                g_free(f->var_ids);
                g_free(f);
            }
        }
        g_array_free(g->factors, TRUE);
    }
    if (g->vars != NULL) g_array_free(g->vars, TRUE);
    if (g->var_index != NULL) g_hash_table_destroy(g->var_index);
    if (g->hints != NULL) g_array_free(g->hints, TRUE);
    if (g->factor_index != NULL) g_hash_table_destroy(g->factor_index);
    if (g->kind_region != NULL) g_hash_table_destroy(g->kind_region);
    g_free(g->uf_parent);
    g_free(g);
}

/* Full-field variable identity key (kind + payload).  A hash is only a
 * bucket selector; identity is the struct itself. */
static OspreyKey var_key_of(uint8_t kind, const OspreyVarPayload *p) {
    OspreyKey k;
    memset(&k, 0, sizeof(k));
    k.tag = 0x564152ULL; /* "VAR" */
    k.w[0] = kind;
    switch (kind) {
    case OSPREY_PRED_PRIMITIVE_VAR:
    case OSPREY_PRED_SCALAR: {
        OspreyKey ck = osprey_chunk_key(&p->chunk);
        k.w[1] = ck.w[0]; k.w[2] = ck.w[1]; k.w[3] = ck.w[2];
        k.w[4] = ck.w[3]; k.w[5] = ck.w[4];
        break;
    }
    case OSPREY_PRED_PRIMITIVE_ACCESS: {
        OspreyKey ck = osprey_chunk_key(&p->prim_access.chunk);
        k.w[1] = ck.w[0]; k.w[2] = ck.w[1]; k.w[3] = ck.w[2];
        k.w[4] = ck.w[3]; k.w[5] = ck.w[4];
        k.w[6] = p->prim_access.insn_pc;
        break;
    }
    case OSPREY_PRED_UNFOLDABLE_HEAP:
    case OSPREY_PRED_FOLDABLE_HEAP: {
        OspreyKey rk = osprey_region_key(&p->heap_fold.region);
        k.w[1] = rk.w[0]; k.w[2] = rk.w[1]; k.w[3] = rk.w[2];
        k.w[4] = p->heap_fold.size;
        break;
    }
    case OSPREY_PRED_HOMO_SEGMENT:
    case OSPREY_PRED_ARRAY: {
        OspreyKey r1 = osprey_region_key(&p->segment.a1.region);
        OspreyKey r2 = osprey_region_key(&p->segment.a2.region);
        k.w[1] = r1.w[0]; k.w[2] = r1.w[1]; k.w[3] = r1.w[2];
        k.w[4] = (uint64_t)p->segment.a1.offset;
        k.w[5] = r2.w[0]; k.w[6] = r2.w[1]; k.w[7] = r2.w[2];
        k.w[8] = (uint64_t)p->segment.a2.offset;
        k.w[9] = (uint64_t)p->segment.size;
        break;
    }
    case OSPREY_PRED_ARRAY_START: {
        OspreyKey rk = osprey_region_key(&p->addr.region);
        k.w[1] = rk.w[0]; k.w[2] = rk.w[1]; k.w[3] = rk.w[2];
        k.w[4] = (uint64_t)p->addr.offset;
        break;
    }
    case OSPREY_PRED_FIELD_OF:
    case OSPREY_PRED_POINTER: {
        OspreyKey ck = osprey_chunk_key(&p->attached.chunk);
        OspreyKey rk = osprey_region_key(&p->attached.base.region);
        k.w[1] = ck.w[0]; k.w[2] = ck.w[1]; k.w[3] = ck.w[2];
        k.w[4] = ck.w[3]; k.w[5] = ck.w[4];
        k.w[6] = rk.w[0]; k.w[7] = rk.w[1];
        k.w[8] = rk.w[2];
        k.w[9] = (uint64_t)p->attached.base.offset;
        break;
    }
    default:
        break;
    }
    return k;
}

/* Intern a predicate variable; returns UINT32_MAX on cap overflow. */
uint32_t osprey_intern_var(OspreyContext *ctx, uint8_t kind,
                           const OspreyVarPayload *payload) {
    OspreyGraph *g = ctx->graph;
    OspreyKey key = var_key_of(kind, payload);
    gpointer existing = g_hash_table_lookup(g->var_index, &key);
    if (existing != NULL) {
        return (uint32_t)(uintptr_t)existing - 1;
    }
    if (g->vars->len >= ctx->config.max_variables) {
        ctx->last_status = OSPREY_LIMIT_EXCEEDED;
        return UINT32_MAX;
    }
    OspreyVar v;
    memset(&v, 0, sizeof(v));
    v.id = g->vars->len;
    v.kind = kind;
    v.payload = *payload;
    g_array_append_val(g->vars, v);
    g_hash_table_insert(g->var_index, osprey_key_new(&key),
                        GSIZE_TO_POINTER((gsize)v.id + 1));
    /* Grow the union-find parent array lazily. */
    if (g->uf_size <= v.id) {
        uint32_t new_size = v.id + 1;
        g->uf_parent = g_realloc(g->uf_parent,
                                 new_size * sizeof(uint32_t));
        for (uint32_t i = g->uf_size; i < new_size; i++) {
            g->uf_parent[i] = i;
        }
        g->uf_size = new_size;
    }
    return v.id;
}

static uint32_t uf_find(OspreyGraph *g, uint32_t x) {
    while (g->uf_parent[x] != x) {
        g->uf_parent[x] = g->uf_parent[g->uf_parent[x]];
        x = g->uf_parent[x];
    }
    return x;
}

static void uf_union(OspreyGraph *g, uint32_t a, uint32_t b) {
    uint32_t ra = uf_find(g, a);
    uint32_t rb = uf_find(g, b);
    if (ra != rb) {
        g->uf_parent[ra] = rb;
    }
}

/* ------------------------------------------------------------------ */
/* Factor creation                                                     */
/* ------------------------------------------------------------------ */

void osprey_factor_add(OspreyContext *ctx, uint16_t rule, uint16_t head_idx,
                       bool negative, double p, const uint32_t *var_ids,
                       uint32_t num_vars) {
    OspreyGraph *g = ctx->graph;
    if (g->factors->len >= ctx->config.max_factors) {
        ctx->last_status = OSPREY_LIMIT_EXCEEDED;
        return;
    }
    /* Deterministic factor identity: full-field key over rule, head,
     * polarity, stage, probability, and the sorted variable set.  The
     * head index is remapped after sorting so bidirectional rules
     * (A→B and B→A) do not dedup-collapse. */
    uint32_t sorted[8] = {0};
    if (num_vars > 8) num_vars = 8;
    for (uint32_t i = 0; i < num_vars; i++) sorted[i] = var_ids[i];
    bool unary_prior = (head_idx == UINT16_MAX);
    uint32_t head_id = unary_prior ? 0 : sorted[head_idx];
    for (uint32_t i = 1; i < num_vars; i++) {
        uint32_t v = sorted[i];
        uint32_t j = i;
        while (j > 0 && sorted[j - 1] > v) {
            sorted[j] = sorted[j - 1];
            j--;
        }
        sorted[j] = v;
    }
    uint32_t sorted_head = 0;
    if (!unary_prior) {
        for (uint32_t i = 0; i < num_vars; i++) {
            if (sorted[i] == head_id) {
                sorted_head = i;
                break;
            }
        }
    } else {
        sorted_head = UINT16_MAX;
    }
    OspreyFactorKey fk;
    memset(&fk, 0, sizeof(fk));
    fk.rule = rule;
    fk.head_idx = (uint16_t)sorted_head;
    fk.negative = negative ? 1 : 0;
    fk.stage = 1;
    memcpy(&fk.p_bits, &p, sizeof(fk.p_bits));
    fk.num_vars = num_vars;
    for (uint32_t i = 0; i < num_vars; i++) fk.var_ids[i] = sorted[i];
    if (g_hash_table_lookup(g->factor_index, &fk) != NULL) {
        return; /* duplicate instance: deterministic merge keeps first */
    }
    OspreyFactor *f = g_new0(OspreyFactor, 1);
    f->id = g->factors->len;
    f->rule = rule;
    f->head_idx = (uint16_t)sorted_head;
    f->negative = negative ? 1 : 0;
    f->stage = 1;
    f->p = p;
    f->num_vars = num_vars;
    f->var_ids = g_memdup(sorted, num_vars * sizeof(uint32_t));
    g_array_append_val(g->factors, f);
    OspreyFactorKey *fk_copy = g_memdup(&fk, sizeof(fk));
    g_hash_table_insert(g->factor_index, fk_copy,
                        GSIZE_TO_POINTER((gsize)f->id + 1));
    for (uint32_t i = 0; i < num_vars; i++) {
        for (uint32_t j = i + 1; j < num_vars; j++) {
            uf_union(g, sorted[i], sorted[j]);
        }
    }
}

guint osprey_factor_key_hash(gconstpointer p) {
    const OspreyFactorKey *k = p;
    uint64_t h = ((uint64_t)k->rule << 48) ^ ((uint64_t)k->head_idx << 32) ^
                 ((uint64_t)k->negative << 16) ^ ((uint64_t)k->stage << 8) ^
                 k->p_bits;
    for (uint32_t i = 0; i < k->num_vars; i++) {
        h ^= (uint64_t)k->var_ids[i] + 0x9e3779b97f4a7c15ULL +
             (h << 6) + (h >> 2);
    }
    return (guint)h;
}

gboolean osprey_factor_key_equal(gconstpointer a, gconstpointer b) {
    const OspreyFactorKey *x = a;
    const OspreyFactorKey *y = b;
    if (x->rule != y->rule || x->head_idx != y->head_idx ||
        x->negative != y->negative || x->stage != y->stage ||
        x->p_bits != y->p_bits || x->num_vars != y->num_vars) {
        return FALSE;
    }
    return memcmp(x->var_ids, y->var_ids,
                  x->num_vars * sizeof(uint32_t)) == 0;
}

/* p_k per §7.2: distinct supporting samples over total sampled paths. */
static double support_ratio(OspreyContext *ctx, uint32_t sample_support) {
    if (ctx->total_samples == 0) return 1.0;
    double r = (double)sample_support / (double)ctx->total_samples;
    if (r > 1.0) r = 1.0;
    return r;
}

/* ------------------------------------------------------------------ */
/* Per-(kind,region) candidate limits                                  */
/* ------------------------------------------------------------------ */

static void kr_account(OspreyContext *ctx, uint8_t kind,
                       const OspreyRegionId *region, uint64_t kept,
                       uint64_t dropped) {
    OspreyGraph *g = ctx->graph;
    OspreyKey ck = osprey_kind_region_key(kind, region);
    OspreyKindRegionCount *c = g_hash_table_lookup(g->kind_region, &ck);
    if (c == NULL) {
        c = g_new0(OspreyKindRegionCount, 1);
        g_hash_table_insert(g->kind_region, osprey_key_new(&ck), c);
    }
    c->kept += kept;
    c->dropped += dropped;
    if (dropped > 0 && g->limit_rows < 4096) {
        g->limit_rows++;
        log_msg("[osprey] [limit] [kind %u] [region %llx] [kept %llu] "
                "[dropped %llu]\n",
                (unsigned)kind,
                (unsigned long long)region->site_offset,
                (unsigned long long)c->kept, (unsigned long long)c->dropped);
    }
}

static bool kr_has_space(OspreyContext *ctx, uint8_t kind,
                         const OspreyRegionId *region) {
    OspreyGraph *g = ctx->graph;
    OspreyKey ck = osprey_kind_region_key(kind, region);
    OspreyKindRegionCount *c = g_hash_table_lookup(g->kind_region, &ck);
    if (c == NULL) return true;
    return c->kept < ctx->config.max_candidates_per_kind_region;
}

/* ------------------------------------------------------------------ */
/* Region extent (observed access bounds or allocation size)          */
/* ------------------------------------------------------------------ */

/* Low/high offsets observed for a region across all fact families. */
static bool region_extent(OspreyContext *ctx, const OspreyRegionId *region,
                          int64_t *lo, int64_t *hi) {
    bool any = false;
    int64_t l = 0, h = 0;
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *f = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        if (!same_region(&f->chunk.address.region, region)) continue;
        int64_t o = f->chunk.address.offset;
        int64_t e = o + (int64_t)f->chunk.size;
        if (!any || o < l) l = o;
        if (!any || e > h) h = e;
        any = true;
    }
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        OspreyBaseFact *b = &g_array_index(ctx->base_facts, OspreyBaseFact, i);
        if (!same_region(&b->chunk.address.region, region)) continue;
        int64_t o = b->chunk.address.offset;
        int64_t e = o + (int64_t)b->chunk.size;
        if (!any || o < l) l = o;
        if (!any || e > h) h = e;
        any = true;
    }
    if (region->kind == OSPREY_REGION_HEAP_SITE) {
        for (guint i = 0; i < ctx->alloc_facts->len; i++) {
            OspreyMallocFact *f = &g_array_index(ctx->alloc_facts,
                                                 OspreyMallocFact, i);
            if (f->site_pc != region->site_offset) continue;
            int64_t e = f->requested_size;
            if (!any) { l = 0; h = e; any = true; }
            else if (e > h) h = e;
        }
    }
    if (!any) return false;
    *lo = l;
    *hi = h;
    return true;
}

/* Aligned starts for a region: observed chunk start offsets. */
static void region_start_offsets(OspreyContext *ctx,
                                 const OspreyRegionId *region,
                                 GArray *offsets /* int64_t */) {
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *f = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        if (!same_region(&f->chunk.address.region, region)) continue;
        int64_t o = f->chunk.address.offset;
        bool seen = false;
        for (guint j = 0; j < offsets->len; j++) {
            if (g_array_index(offsets, int64_t, j) == o) { seen = true; break; }
        }
        if (!seen) g_array_append_val(offsets, o);
    }
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        OspreyBaseFact *b = &g_array_index(ctx->base_facts, OspreyBaseFact, i);
        if (!same_region(&b->chunk.address.region, region)) continue;
        int64_t o = b->chunk.address.offset;
        bool seen = false;
        for (guint j = 0; j < offsets->len; j++) {
            if (g_array_index(offsets, int64_t, j) == o) { seen = true; break; }
        }
        if (!seen) g_array_append_val(offsets, o);
    }
    insertion_sort_i64(offsets);
}

/* ------------------------------------------------------------------ */
/* R08/R09: alloc-unit facts per heap site                             */
/* ------------------------------------------------------------------ */

static bool alloc_unit_for_region(OspreyContext *ctx,
                                  const OspreyRegionId *region,
                                  int64_t *unit_out, bool *singleton_out) {
    /* sorted distinct successful requested sizes at this site */
    GArray *sizes = g_array_new(FALSE, FALSE, sizeof(int64_t));
    for (guint i = 0; i < ctx->alloc_facts->len; i++) {
        OspreyMallocFact *f = &g_array_index(ctx->alloc_facts,
                                             OspreyMallocFact, i);
        if (f->site_pc != region->site_offset) continue;
        int64_t s = (int64_t)f->requested_size;
        bool seen = false;
        for (guint j = 0; j < sizes->len; j++) {
            if (g_array_index(sizes, int64_t, j) == s) { seen = true; break; }
        }
        if (!seen) g_array_append_val(sizes, s);
    }
    if (sizes->len == 0) {
        g_array_free(sizes, TRUE);
        return false;
    }
    insertion_sort_i64(sizes);
    if (sizes->len == 1) {
        /* R08 ConstantAllocSize */
        *unit_out = g_array_index(sizes, int64_t, 0);
        if (singleton_out) *singleton_out = true;
    } else {
        /* R09 AllocUnit: gcd of successive size differences */
        int64_t g = 0;
        for (guint i = 1; i < sizes->len; i++) {
            int64_t d = g_array_index(sizes, int64_t, i) -
                        g_array_index(sizes, int64_t, i - 1);
            g = (g == 0) ? d : gcd_i64(g, d);
        }
        if (g == 0) {
            g_array_free(sizes, TRUE);
            return false;
        }
        *unit_out = g;
        if (singleton_out) *singleton_out = false;
    }
    g_array_free(sizes, TRUE);
    return true;
}

/* ------------------------------------------------------------------ */
/* R10-R12 hint extraction                                             */
/* ------------------------------------------------------------------ */

static void hint_add(OspreyContext *ctx, OspreyAddress a1, OspreyAddress a2,
                     int64_t s, uint8_t kind, uint64_t instances) {
    OspreyGraph *g = ctx->graph;
    for (guint i = 0; i < g->hints->len; i++) {
        OspreyHint *e = &g_array_index(g->hints, OspreyHint, i);
        if (e->kind == kind && e->size == s &&
            address_equal(&e->a1, &a1) && address_equal(&e->a2, &a2)) {
            if (UINT64_MAX - e->instances < instances) {
                e->instances = UINT64_MAX;
            } else {
                e->instances += instances;
            }
            if (UINT64_MAX - g->hint_instances < instances) {
                g->hint_instances = UINT64_MAX;
            } else {
                g->hint_instances += instances;
            }
            return;
        }
    }
    OspreyHint h;
    memset(&h, 0, sizeof(h));
    h.a1 = a1;
    h.a2 = a2;
    h.size = s;
    h.kind = kind;
    h.instances = instances;
    g_array_append_val(g->hints, h);
    if (UINT64_MAX - g->hint_instances < instances) {
        g->hint_instances = UINT64_MAX;
    } else {
        g->hint_instances += instances;
    }
}

/* R10-R12 are materialized by osprey-relations.c.  The graph stage only
 * transfers those immutable hint rows; it must not reconstruct them from
 * class-specific F01 rows or from insertion order. */
static void closure_r10(OspreyContext *ctx) {
    if (ctx->relations == NULL) return;
    for (guint i = 0; i < ctx->relations->r10_data_flow->len; i++) {
        const OspreyHintRelation *r = &g_array_index(
            ctx->relations->r10_data_flow, OspreyHintRelation, i);
        hint_add(ctx, r->a1, r->a2, r->size,
                 OSPREY_RELATION_DATA_FLOW, r->witness_count);
    }
}

static void closure_r11(OspreyContext *ctx) {
    if (ctx->relations == NULL) return;
    for (guint i = 0; i < ctx->relations->r11_unified_access->len; i++) {
        const OspreyHintRelation *r = &g_array_index(
            ctx->relations->r11_unified_access, OspreyHintRelation, i);
        hint_add(ctx, r->a1, r->a2, r->size,
                 OSPREY_RELATION_UNIFIED_ACCESS, r->witness_count);
    }
}

static void closure_r12(OspreyContext *ctx) {
    if (ctx->relations == NULL) return;
    for (guint i = 0; i < ctx->relations->r12_points_to->len; i++) {
        const OspreyHintRelation *r = &g_array_index(
            ctx->relations->r12_points_to, OspreyHintRelation, i);
        hint_add(ctx, r->a1, r->a2, r->size,
                 OSPREY_RELATION_POINTS_TO, r->witness_count);
    }
}

/* ------------------------------------------------------------------ */
/* Static factor instantiation (CA/CB/CC/CD base rules)                */
/* ------------------------------------------------------------------ */

#define P_UP 0.8
#define P_DN 0.2

/* CA01: Access(i,v,k) : p_k↑ PrimitiveVar(v) */
static void instantiate_ca01(OspreyContext *ctx) {
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *a = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        OspreyVarPayload pv;
        memset(&pv, 0, sizeof(pv));
        pv.chunk = a->chunk;
        uint32_t v = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pv);
        if (v == UINT32_MAX) continue;
        double pk = support_ratio(ctx, a->sample_support);
        uint32_t ids[1] = { v };
        osprey_factor_add(ctx, OSPREY_RULE_CA01, 0, false, pk, ids, 1);
    }
}

/* CA02/CA03: adjacency/overlap mutual support between primitives. */
static void instantiate_ca02_ca03(OspreyContext *ctx) {
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *a = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        for (guint j = i + 1; j < ctx->access_facts->len; j++) {
            OspreyAccessFact *b = &g_array_index(ctx->access_facts,
                                                 OspreyAccessFact, j);
            int64_t d;
            if (!offset_between(&b->chunk.address, &a->chunk.address, &d))
                continue;
            bool adjacent = (d == (int64_t)a->chunk.size);
            bool overlap = (d >= 0 && d < (int64_t)a->chunk.size);
            if (!adjacent && !overlap) continue;
            OspreyVarPayload pa, pb;
            memset(&pa, 0, sizeof(pa)); pa.chunk = a->chunk;
            memset(&pb, 0, sizeof(pb)); pb.chunk = b->chunk;
            uint32_t va = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pa);
            uint32_t vb = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pb);
            if (va == UINT32_MAX || vb == UINT32_MAX) continue;
            uint32_t ids[2] = { va, vb };
            if (adjacent) {
                /* mutual positive support, split into two factors */
                osprey_factor_add(ctx, OSPREY_RULE_CA02, 0, false, P_UP, ids, 2);
                osprey_factor_add(ctx, OSPREY_RULE_CA02, 1, false, P_UP, ids, 2);
            }
            if (overlap) {
                osprey_factor_add(ctx, OSPREY_RULE_CA03, 0, true, P_DN, ids, 2);
                osprey_factor_add(ctx, OSPREY_RULE_CA03, 1, true, P_DN, ids, 2);
            }
        }
    }
}

/* CA04/CA05: primitive <-> primitive-access edges. */
static void instantiate_ca04_ca05(OspreyContext *ctx) {
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *a = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        OspreyVarPayload pv;
        memset(&pv, 0, sizeof(pv));
        pv.chunk = a->chunk;
        uint32_t v = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pv);
        if (v == UINT32_MAX) continue;
        OspreyVarPayload pa;
        memset(&pa, 0, sizeof(pa));
        pa.prim_access.chunk = a->chunk;
        pa.prim_access.insn_pc = a->pc;
        uint32_t acc = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_ACCESS, &pa);
        if (acc == UINT32_MAX) continue;
        double pk = support_ratio(ctx, a->sample_support);
        uint32_t ids[2] = { acc, v };
        /* CA04: PrimitiveVar(v) --p↑--> PrimitiveAccess(i,v) */
        osprey_factor_add(ctx, OSPREY_RULE_CA04, 0, false, pk, ids, 2);
        /* CA05: PrimitiveAccess(i,v) --p↑--> PrimitiveVar(v) */
        osprey_factor_add(ctx, OSPREY_RULE_CA05, 1, false, pk, ids, 2);
    }
}

/* CA06: AccessSingleChunk(i,r) ∧ Access(i,v,k) : Scalar(v) */
static void instantiate_ca06(OspreyContext *ctx) {
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *a = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        /* count distinct chunks for (insn, region) */
        uint32_t distinct = 0;
        for (guint j = 0; j < ctx->access_facts->len; j++) {
            OspreyAccessFact *b = &g_array_index(ctx->access_facts,
                                                 OspreyAccessFact, j);
            if (b->pc != a->pc) continue;
            if (!same_region(&b->chunk.address.region,
                             &a->chunk.address.region))
                continue;
            distinct++;
            if (distinct > 1) break;
        }
        if (distinct != 1) continue;
        OspreyVarPayload pv;
        memset(&pv, 0, sizeof(pv));
        pv.chunk = a->chunk;
        uint32_t v = osprey_intern_var(ctx, OSPREY_PRED_SCALAR, &pv);
        if (v == UINT32_MAX) continue;
        OspreyVarPayload pa;
        memset(&pa, 0, sizeof(pa));
        pa.prim_access.chunk = a->chunk;
        pa.prim_access.insn_pc = a->pc;
        uint32_t acc = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_ACCESS, &pa);
        if (acc == UINT32_MAX) continue;
        double pk = support_ratio(ctx, a->sample_support);
        uint32_t ids[2] = { acc, v };
        osprey_factor_add(ctx, OSPREY_RULE_CA06, 1, false, pk, ids, 2);
    }
}

/* CA08: Scalar(v) ↔ p_dn FieldOf(v, base-of-v) is secondary (needs
 * base candidates); the CD06 factors carry the FieldOf construction.
 * CA07 requires two instructions with single-chunk regions; we instantiate
 * the mutual Scalar support for adjacent chunks that are both
 * single-chunk accessed (bounded pair loop). */
static void instantiate_ca07(OspreyContext *ctx) {
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *a = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        for (guint j = i + 1; j < ctx->access_facts->len; j++) {
            OspreyAccessFact *b = &g_array_index(ctx->access_facts,
                                                 OspreyAccessFact, j);
            if (a->pc == b->pc) continue;
            int64_t d;
            if (!offset_between(&b->chunk.address, &a->chunk.address, &d))
                continue;
            if (d != (int64_t)a->chunk.size) continue; /* adjacent */
            /* single-chunk check for both instructions */
            uint32_t da = 0, db = 0;
            for (guint k = 0; k < ctx->access_facts->len; k++) {
                OspreyAccessFact *c = &g_array_index(ctx->access_facts,
                                                     OspreyAccessFact, k);
                if (c->pc == a->pc &&
                    same_region(&c->chunk.address.region,
                                &a->chunk.address.region))
                    da++;
                if (c->pc == b->pc &&
                    same_region(&c->chunk.address.region,
                                &b->chunk.address.region))
                    db++;
                if (da > 1 || db > 1) break;
            }
            if (da != 1 || db != 1) continue;
            OspreyVarPayload pva, pvb;
            memset(&pva, 0, sizeof(pva)); pva.chunk = a->chunk;
            memset(&pvb, 0, sizeof(pvb)); pvb.chunk = b->chunk;
            uint32_t va = osprey_intern_var(ctx, OSPREY_PRED_SCALAR, &pva);
            uint32_t vb = osprey_intern_var(ctx, OSPREY_PRED_SCALAR, &pvb);
            if (va == UINT32_MAX || vb == UINT32_MAX) continue;
            double pk_a = support_ratio(ctx, a->sample_support);
            double pk_b = support_ratio(ctx, b->sample_support);
            double pk = P_UP * (pk_a < pk_b ? pk_a : pk_b) *
                        (1.0 - (pk_a > pk_b ? pk_a - pk_b : pk_b - pk_a));
            if (pk < P_DN) pk = P_DN;
            if (pk > P_UP) pk = P_UP;
            uint32_t ids[2] = { va, vb };
            osprey_factor_add(ctx, OSPREY_RULE_CA07, 0, false, pk, ids, 2);
            osprey_factor_add(ctx, OSPREY_RULE_CA07, 1, false, pk, ids, 2);
        }
    }
}

/* CB01: MayArray(a,k,s) -> Array(a, a+s*k, s) ∧ ArrayStart(a).  The
 * may-array facts carry element size and count; stride is element_size. */
static void instantiate_cb01(OspreyContext *ctx) {
    for (guint i = 0; i < ctx->mayarray_facts->len; i++) {
        OspreyMayArrayFact *m = &g_array_index(ctx->mayarray_facts,
                                               OspreyMayArrayFact, i);
        if (m->element_size == 0) continue;
        int64_t s = (int64_t)m->element_size;
        uint64_t n = (uint64_t)m->element_count;
        uint64_t span_u;
        if (!osprey_check_mul((uint64_t)s, n, &span_u)) continue;
        if (span_u == 0 || span_u > INT64_MAX) continue;
        int64_t span = (int64_t)span_u;
        OspreyAddress a2 = m->start;
        int64_t off2;
        if (!osprey_check_add(a2.offset, span, &off2)) continue;
        a2.offset = off2;
        OspreyVarPayload pa;
        memset(&pa, 0, sizeof(pa));
        pa.segment.a1 = m->start;
        pa.segment.a2 = a2;
        pa.segment.size = s;
        uint32_t v_arr = osprey_intern_var(ctx, OSPREY_PRED_ARRAY, &pa);
        if (v_arr == UINT32_MAX) continue;
        OspreyVarPayload ps;
        memset(&ps, 0, sizeof(ps));
        ps.addr = m->start;
        uint32_t v_start = osprey_intern_var(ctx, OSPREY_PRED_ARRAY_START, &ps);
        if (v_start == UINT32_MAX) continue;
        double pk = support_ratio(ctx, m->sample_support);
        uint32_t ids[2] = { v_arr, v_start };
        osprey_factor_add(ctx, OSPREY_RULE_CB01, 0, false, pk, ids, 2);
        osprey_factor_add(ctx, OSPREY_RULE_CB01, 1, false, pk, ids, 2);
    }
}

/* CC01/CC02: constant alloc size / alloc unit per heap site. */
static void instantiate_cc01_cc02(OspreyContext *ctx) {
    GHashTable *sites = g_hash_table_new_full(g_direct_hash, g_direct_equal,
                                              NULL, NULL);
    for (guint i = 0; i < ctx->alloc_facts->len; i++) {
        OspreyMallocFact *f = &g_array_index(ctx->alloc_facts,
                                             OspreyMallocFact, i);
        if (g_hash_table_lookup(sites, GSIZE_TO_POINTER((gsize)f->site_pc)) !=
            NULL)
            continue;
        g_hash_table_insert(sites, GSIZE_TO_POINTER((gsize)f->site_pc),
                            GSIZE_TO_POINTER(1));
        OspreyRegionId h;
        h.kind = OSPREY_REGION_HEAP_SITE;
        h.code_image_id = 0;
        h.site_offset = f->site_pc;
        int64_t unit;
        bool singleton = false;
        if (!alloc_unit_for_region(ctx, &h, &unit, &singleton)) continue;
        if (unit < 0) continue;
        OspreyVarPayload pf;
        memset(&pf, 0, sizeof(pf));
        pf.heap_fold.region = h;
        pf.heap_fold.size = (uint64_t)unit;
        uint32_t vfold = osprey_intern_var(ctx, OSPREY_PRED_FOLDABLE_HEAP, &pf);
        if (vfold == UINT32_MAX) continue;
        uint32_t ids[1] = { vfold };
        /* CC02: FoldableHeap(i,s) prior (positive support); CC01's
         * UnfoldableHeap(i,s) ∧ FoldableHeap(i,0) is emitted when a
         * constant size exists (sizes->len == 1 handled by the same
         * helper; emit the CC01 pair then). */
        if (singleton) {
            /* CC01: ConstantAllocSize(i,s) : p↑ UnfoldableHeap(i,s) ∧
             * FoldableHeap(i,0); antecedent is a deterministic fact, so
             * each consequent is a unary positive factor. */
            OspreyVarPayload pu;
            memset(&pu, 0, sizeof(pu));
            pu.heap_fold.region = h;
            pu.heap_fold.size = (uint64_t)unit;
            uint32_t vunf = osprey_intern_var(ctx, OSPREY_PRED_UNFOLDABLE_HEAP, &pu);
            OspreyVarPayload pz;
            memset(&pz, 0, sizeof(pz));
            pz.heap_fold.region = h;
            pz.heap_fold.size = 0; /* FoldableHeap(i,0): no foldable tail */
            uint32_t vzero = osprey_intern_var(ctx, OSPREY_PRED_FOLDABLE_HEAP, &pz);
            if (vunf != UINT32_MAX) {
                uint32_t ids1[1] = { vunf };
                osprey_factor_add(ctx, OSPREY_RULE_CC01, UINT16_MAX, false, P_UP,
                           ids1, 1);
            }
            if (vzero != UINT32_MAX) {
                uint32_t ids1[1] = { vzero };
                osprey_factor_add(ctx, OSPREY_RULE_CC01, UINT16_MAX, false, P_UP,
                           ids1, 1);
            }
        }
        /* CC02: AllocUnit(i,s) -> FoldableHeap(i,s) unary prior */
        osprey_factor_add(ctx, OSPREY_RULE_CC02, UINT16_MAX, false, P_UP, ids, 1);
    }
    g_hash_table_destroy(sites);
}

/* CC03: PrimitiveVar(v) in heap H_i -> UnfoldableHeap(i, o+s). */
static void instantiate_cc03(OspreyContext *ctx) {
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *a = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        if (a->chunk.address.region.kind != OSPREY_REGION_HEAP_SITE)
            continue;
        OspreyVarPayload pv;
        memset(&pv, 0, sizeof(pv));
        pv.chunk = a->chunk;
        uint32_t v = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pv);
        if (v == UINT32_MAX) continue;
        int64_t end;
        if (!osprey_check_add(a->chunk.address.offset,
                              (int64_t)a->chunk.size, &end))
            continue;
        OspreyVarPayload ph;
        memset(&ph, 0, sizeof(ph));
        ph.heap_fold.region = a->chunk.address.region;
        ph.heap_fold.size = (uint64_t)end;
        uint32_t u = osprey_intern_var(ctx, OSPREY_PRED_UNFOLDABLE_HEAP, &ph);
        if (u == UINT32_MAX) continue;
        uint32_t ids[2] = { v, u };
        osprey_factor_add(ctx, OSPREY_RULE_CC03, 1, false, P_UP, ids, 2);
    }
}

/* CD06: BaseAddr(i,v1,v2.a) ∧ Accessed(v1) ∧ Accessed(v2) ->
 * FieldOf(v1, v2.a). */
static void instantiate_cd06(OspreyContext *ctx) {
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        OspreyBaseFact *b = &g_array_index(ctx->base_facts, OspreyBaseFact, i);
        OspreyVarPayload pv;
        memset(&pv, 0, sizeof(pv));
        pv.chunk = b->chunk;
        uint32_t v = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pv);
        if (v == UINT32_MAX) continue;
        OspreyVarPayload pf;
        memset(&pf, 0, sizeof(pf));
        pf.attached.chunk = b->chunk;
        pf.attached.base = b->base;
        uint32_t f = osprey_intern_var(ctx, OSPREY_PRED_FIELD_OF, &pf);
        if (f == UINT32_MAX) continue;
        uint32_t ids[2] = { v, f };
        /* CD06: BaseAddr(i,v1,v2.a) ∧ Accessed(v1) ∧ Accessed(v2)
         * -> FieldOf(v1,v2.a); antecedent facts are committed, so the
         * binary implication PrimitiveVar(v1) -> FieldOf(v1,v2.a) with
         * the §7.1 generic potential. */
        osprey_factor_add(ctx, OSPREY_RULE_CD06, 1, false, P_UP, ids, 2);
    }
}

/* CD11: PointsTo(v1, v2.a) ∧ Accessed(v1) ∧ Accessed(v2) ->
 * Pointer(v1, v2.a). */
static void instantiate_cd11(OspreyContext *ctx) {
    for (guint i = 0; i < ctx->points_facts->len; i++) {
        OspreyPointsToFact *p = &g_array_index(ctx->points_facts,
                                               OspreyPointsToFact, i);
        OspreyVarPayload pv;
        memset(&pv, 0, sizeof(pv));
        pv.chunk = p->pointer_chunk;
        uint32_t v1 = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pv);
        if (v1 == UINT32_MAX) continue;
        OspreyVarPayload pp;
        memset(&pp, 0, sizeof(pp));
        pp.attached.chunk = p->pointer_chunk;
        pp.attached.base = p->target;
        uint32_t po = osprey_intern_var(ctx, OSPREY_PRED_POINTER, &pp);
        if (po == UINT32_MAX) continue;
        uint32_t ids[2] = { v1, po };
        /* CD11: PointsTo(v1,v2.a) ∧ Accessed(v1) ∧ Accessed(v2)
         * -> Pointer(v1,v2.a); facts already committed, so binary
         * PrimitiveVariable(v1) -> Pointer(v1,v2.a). */
        osprey_factor_add(ctx, OSPREY_RULE_CD11, 1, false, P_UP, ids, 2);
    }
}

/* CD10: FieldOf(v,a1) ↔ p↓ FieldOf(v,a2) for a1 != a2 (exclusion). */
static void instantiate_cd10(OspreyContext *ctx) {
    OspreyGraph *g = ctx->graph;
    for (guint i = 0; i < g->vars->len; i++) {
        OspreyVar *v1 = &g_array_index(g->vars, OspreyVar, i);
        if (v1->kind != OSPREY_PRED_FIELD_OF) continue;
        for (guint j = i + 1; j < g->vars->len; j++) {
            OspreyVar *v2 = &g_array_index(g->vars, OspreyVar, j);
            if (v2->kind != OSPREY_PRED_FIELD_OF) continue;
            if (!chunk_equal(&v1->payload.attached.chunk,
                             &v2->payload.attached.chunk))
                continue;
            if (address_equal(&v1->payload.attached.base,
                              &v2->payload.attached.base))
                continue;
            uint32_t ids[2] = { v1->id, v2->id };
            osprey_factor_add(ctx, OSPREY_RULE_CD10, 0, true, P_DN, ids, 2);
            osprey_factor_add(ctx, OSPREY_RULE_CD10, 1, true, P_DN, ids, 2);
        }
    }
}

/* CD01/CD02/CD03: hint -> HomoSegment(a1,a2,s). */
static void instantiate_cd01_03(OspreyContext *ctx) {
    OspreyGraph *g = ctx->graph;
    for (guint i = 0; i < g->hints->len; i++) {
        OspreyHint *h = &g_array_index(g->hints, OspreyHint, i);
        if (!kr_has_space(ctx, OSPREY_PRED_HOMO_SEGMENT, &h->a1.region)) {
            kr_account(ctx, OSPREY_PRED_HOMO_SEGMENT, &h->a1.region, 0, 1);
            continue;
        }
        /* §9.3: align starts to observed chunk starts */
        GArray *starts = g_array_new(FALSE, FALSE, sizeof(int64_t));
        region_start_offsets(ctx, &h->a1.region, starts);
        bool aligned = false;
        for (guint k = 0; k < starts->len; k++) {
            if (g_array_index(starts, int64_t, k) == h->a1.offset) {
                aligned = true;
                break;
            }
        }
        g_array_free(starts, TRUE);
        if (!aligned) {
            kr_account(ctx, OSPREY_PRED_HOMO_SEGMENT, &h->a1.region, 0, 1);
            continue;
        }
        OspreyVarPayload pv;
        memset(&pv, 0, sizeof(pv));
        pv.segment.a1 = h->a1;
        pv.segment.a2 = h->a2;
        pv.segment.size = h->size;
        uint32_t v = osprey_intern_var(ctx, OSPREY_PRED_HOMO_SEGMENT, &pv);
        if (v == UINT32_MAX) continue;
        double ps = P_UP;
        if (ctx->total_samples > 0) {
            double r = (double)h->instances / (double)ctx->total_samples;
            ps = P_UP * (r > 1.0 ? 1.0 : r);
            if (ps < P_DN) ps = P_DN;
        }
        uint16_t rule = (h->kind == 0) ? OSPREY_RULE_CD01 :
                        (h->kind == 1) ? OSPREY_RULE_CD03 :
                                         OSPREY_RULE_CD02;
        uint32_t ids[1] = { v };
        osprey_factor_add(ctx, rule, 0, false, ps, ids, 1);
        kr_account(ctx, OSPREY_PRED_HOMO_SEGMENT, &h->a1.region, 1, 0);
    }
}

/* CD04 closure: from (a1,a1',s1) and (a2,a2',s2) with 0 < a2-a1 < s1,
 * extend HomoSegment(a1,a1',(a2-a1)+s2); negative direction excludes.
 * Instances are bounded by the candidate cap. */
static void closure_cd04(OspreyContext *ctx) {
    OspreyGraph *g = ctx->graph;
    guint base_len = g->hints->len;
    for (guint i = 0; i < base_len; i++) {
        OspreyHint *h1 = &g_array_index(g->hints, OspreyHint, i);
        for (guint j = 0; j < base_len; j++) {
            if (i == j) continue;
            OspreyHint *h2 = &g_array_index(g->hints, OspreyHint, j);
            int64_t d;
            if (!offset_between(&h2->a1, &h1->a1, &d)) continue;
            if (!(d > 0 && d < h1->size)) continue;
            if (!same_region_addr(&h1->a1, &h2->a1)) continue;
            /* union length: (a2-a1) + s2 */
            int64_t len;
            if (!osprey_check_add(d, h2->size, &len)) continue;
            if (len <= 0) continue;
            if (!kr_has_space(ctx, OSPREY_PRED_HOMO_SEGMENT, &h1->a1.region)) {
                kr_account(ctx, OSPREY_PRED_HOMO_SEGMENT, &h1->a1.region, 0, 1);
                continue;
            }
            /* cap extended length to observed region extent (§9.3) */
            int64_t lo, hi;
            if (!region_extent(ctx, &h1->a1.region, &lo, &hi)) continue;
            if (h1->a1.offset < lo) continue;
            int64_t end;
            if (!osprey_check_add(h1->a1.offset, len, &end)) continue;
            if (end > hi) continue;
            /* a1 starts are observed chunk starts by construction
             * (hints only reference observed chunk addresses) */
            OspreyAddress a1p = h1->a2;
            OspreyVarPayload pv;
            memset(&pv, 0, sizeof(pv));
            pv.segment.a1 = h1->a1;
            pv.segment.a2 = a1p;
            pv.segment.size = len;
            uint32_t v = osprey_intern_var(ctx, OSPREY_PRED_HOMO_SEGMENT, &pv);
            if (v == UINT32_MAX) continue;
            uint32_t ids[1] = { v };
            osprey_factor_add(ctx, OSPREY_RULE_CD04, 0, false, P_UP, ids, 1);
            g->cd04_extensions++;
        }
    }
}

/* ------------------------------------------------------------------ */
/* Secondary deterministic rules (CB02-CB09, CC04/CC05, CD07, CD08)     */
/* ------------------------------------------------------------------ */

/* Region buckets: key -> GArray of var ids (freed with bucket_free). */
static void bucket_free(gpointer p) {
    g_array_free((GArray *)p, TRUE);
}

static GHashTable *bucket_new(void)
{
    return g_hash_table_new_full(osprey_key_hash, osprey_key_equal,
                                 osprey_key_free, bucket_free);
}

static void bucket_add(GHashTable *b, const OspreyRegionId *r, uint32_t id)
{
    OspreyKey k = osprey_region_key(r);
    GArray *arr = g_hash_table_lookup(b, &k);
    if (arr == NULL) {
        arr = g_array_new(FALSE, FALSE, sizeof(uint32_t));
        g_hash_table_insert(b, osprey_key_new(&k), arr);
    }
    g_array_append_val(arr, id);
}

static void bucket_region_arrays(GHashTable *b, const OspreyRegionId *r,
                                 GArray **out)
{
    OspreyKey k = osprey_region_key(r);
    *out = g_hash_table_lookup(b, &k);
}

/* Array var helpers: extract (lo, hi, stride) from the segment payload. */
static bool array_interval(const OspreyVar *v, const OspreyAddress **lo,
                           const OspreyAddress **hi, int64_t *stride)
{
    if (v->kind != OSPREY_PRED_ARRAY) return false;
    *lo = &v->payload.segment.a1;
    *hi = &v->payload.segment.a2;
    *stride = v->payload.segment.size;
    return *stride > 0;
}

/* CB02: AccessMultiChunks(i,r) with Lo/HiAddrAccessed ->
 * PrimitiveAccess(v1) ∧ PrimitiveAccess(v2) --p↑--> Array(v1.a,v2.a+v2.s,v1.s).
 * One factor per multi-chunk (insn, region); head is the Array var. */
static void secondary_cb02(OspreyContext *ctx)
{
    GHashTable *groups = g_hash_table_new_full(osprey_key_hash,
                                               osprey_key_equal,
                                               osprey_key_free, NULL);
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *a = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        OspreyKey gk = osprey_pc_region_key(a->pc,
                                            &a->chunk.address.region);
        if (g_hash_table_lookup(groups, &gk) != NULL)
            continue;
        g_hash_table_insert(groups, osprey_key_new(&gk), GSIZE_TO_POINTER(1));
        /* distinct chunks for (insn, region) */
        int64_t lo_off = 0, hi_end = 0;
        bool any = false;
        uint32_t distinct = 0;
        OspreyChunk lo_chunk, hi_chunk;
        memset(&lo_chunk, 0, sizeof(lo_chunk));
        memset(&hi_chunk, 0, sizeof(hi_chunk));
        for (guint j = 0; j < ctx->access_facts->len; j++) {
            OspreyAccessFact *b = &g_array_index(ctx->access_facts,
                                                 OspreyAccessFact, j);
            if (b->pc != a->pc) continue;
            if (!same_region(&b->chunk.address.region,
                             &a->chunk.address.region))
                continue;
            /* count distinct offsets (chunks) */
            bool seen = false;
            for (guint k = 0; k < j; k++) {
                OspreyAccessFact *c = &g_array_index(ctx->access_facts,
                                                     OspreyAccessFact, k);
                if (c->pc != b->pc) continue;
                if (same_region(&c->chunk.address.region,
                                &b->chunk.address.region) &&
                    c->chunk.address.offset == b->chunk.address.offset &&
                    c->chunk.size == b->chunk.size) {
                    seen = true;
                    break;
                }
            }
            if (!seen) {
                distinct++;
                int64_t e = b->chunk.address.offset + (int64_t)b->chunk.size;
                if (!any || b->chunk.address.offset < lo_off) {
                    lo_off = b->chunk.address.offset;
                    lo_chunk = b->chunk;
                }
                if (!any || e > hi_end) {
                    hi_end = e;
                    hi_chunk = b->chunk;
                }
                any = true;
            }
        }
        if (distinct <= 1) continue; /* R03 single-chunk; no CB02 */
        /* v1 = lo chunk, v2 = hi chunk (hi address = hi end - hi size) */
        OspreyAddress a1 = lo_chunk.address;
        OspreyAddress a2 = hi_chunk.address;
        int64_t hi_off = hi_end - (int64_t)hi_chunk.size;
        a2.offset = hi_off;
        int64_t stride = (int64_t)lo_chunk.size;
        if (stride <= 0) continue;
        /* guard hi-lo >= stride (§9.2) */
        if (!osprey_check_sub(a2.offset, a1.offset, &lo_off)) continue;
        if (lo_off < stride) continue;
        /* Array candidate, region-capped */
        if (!kr_has_space(ctx, OSPREY_PRED_ARRAY, &a1.region)) {
            kr_account(ctx, OSPREY_PRED_ARRAY, &a1.region, 0, 1);
            continue;
        }
        OspreyVarPayload pa1, pa2, parr;
        memset(&pa1, 0, sizeof(pa1));
        pa1.prim_access.chunk = lo_chunk;
        pa1.prim_access.insn_pc = a->pc;
        memset(&pa2, 0, sizeof(pa2));
        pa2.prim_access.chunk = hi_chunk;
        pa2.prim_access.insn_pc = a->pc;
        memset(&parr, 0, sizeof(parr));
        parr.segment.a1 = a1;
        parr.segment.a2 = a2;
        parr.segment.size = (uint64_t)stride;
        uint32_t v1 = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_ACCESS, &pa1);
        uint32_t v2 = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_ACCESS, &pa2);
        uint32_t varr = osprey_intern_var(ctx, OSPREY_PRED_ARRAY, &parr);
        if (v1 == UINT32_MAX || v2 == UINT32_MAX ||
            varr == UINT32_MAX) continue;
        uint32_t ids[3] = { v1, v2, varr };
        osprey_factor_add(ctx, OSPREY_RULE_CB02, 2, false, P_UP, ids, 3);
        kr_account(ctx, OSPREY_PRED_ARRAY, &a1.region, 1, 0);
    }
    g_hash_table_destroy(groups);
}

/* CB03/CB04: overlapping interval pairs (same region).  Bounded: skip a
 * region entirely when its array count exceeds the cap (limit row). */
#define SECONDARY_MAX_ARRAY_PAIRS_REGION 512u

static void cb03_cb04_pairs(OspreyContext *ctx, GArray *arrays)
{
    if (arrays->len > SECONDARY_MAX_ARRAY_PAIRS_REGION) {
        OspreyVar *first = &g_array_index(arrays, OspreyVar, 0);
        kr_account(ctx, OSPREY_PRED_ARRAY, &first->payload.segment.a1.region,
                   0, arrays->len);
        return;
    }
    for (guint i = 0; i < arrays->len; i++) {
        OspreyVar *A = &g_array_index(arrays, OspreyVar, i);
        const OspreyAddress *a1l, *a1h;
        int64_t s1;
        if (!array_interval(A, &a1l, &a1h, &s1)) continue;
        if (a1h->offset <= a1l->offset) continue;
        for (guint j = i + 1; j < arrays->len; j++) {
            OspreyVar *B = &g_array_index(arrays, OspreyVar, j);
            const OspreyAddress *a2l, *a2h;
            int64_t s2;
            if (!array_interval(B, &a2l, &a2h, &s2)) continue;
            if (a2h->offset <= a2l->offset) continue;
            /* ordering a1l <= a2l <= a1h <= a2h (same region by bucket) */
            if (a2l->offset < a1l->offset) continue;
            if (a1h->offset < a2l->offset) continue;
            if (a2h->offset < a1h->offset) continue;
            int64_t d;
            if (!osprey_check_sub(a2l->offset, a1l->offset, &d)) continue;
            bool compatible = (s1 == s2) && (d % s1 == 0);
            if (compatible) {
                /* CB03: mutual support + union array */
                uint32_t ids[2] = { A->id, B->id };
                osprey_factor_add(ctx, OSPREY_RULE_CB03, 0, false, P_UP, ids, 2);
                osprey_factor_add(ctx, OSPREY_RULE_CB03, 1, false, P_UP, ids, 2);
                if (kr_has_space(ctx, OSPREY_PRED_ARRAY, &a1l->region)) {
                    int64_t span;
                    if (osprey_check_sub(a2h->offset, a1l->offset, &span) &&
                        span >= s1) {
                        OspreyVarPayload pc;
                        memset(&pc, 0, sizeof(pc));
                        pc.segment.a1 = *a1l;
                        pc.segment.a2 = *a2h;
                        pc.segment.size = (uint64_t)s1;
                        uint32_t vc = osprey_intern_var(ctx, OSPREY_PRED_ARRAY, &pc);
                        if (vc != UINT32_MAX) {
                            uint32_t ids3[3] = { A->id, B->id, vc };
                            osprey_factor_add(ctx, OSPREY_RULE_CB03, 2, false,
                                       P_UP, ids3, 3);
                            kr_account(ctx, OSPREY_PRED_ARRAY,
                                       &a1l->region, 1, 0);
                        }
                    }
                }
            } else {
                /* CB04: exclusion + two sub-array supports */
                uint32_t ids[2] = { A->id, B->id };
                osprey_factor_add(ctx, OSPREY_RULE_CB04, 0, true, P_DN, ids, 2);
                osprey_factor_add(ctx, OSPREY_RULE_CB04, 1, true, P_DN, ids, 2);
                if (kr_has_space(ctx, OSPREY_PRED_ARRAY, &a1l->region)) {
                    /* Array(a1l,a2l,s1) */
                    int64_t len1;
                    if (osprey_check_sub(a2l->offset, a1l->offset, &len1) &&
                        len1 >= s1) {
                        OspreyVarPayload pc;
                        memset(&pc, 0, sizeof(pc));
                        pc.segment.a1 = *a1l;
                        pc.segment.a2 = *a2l;
                        pc.segment.size = (uint64_t)s1;
                        uint32_t vc = osprey_intern_var(ctx, OSPREY_PRED_ARRAY, &pc);
                        if (vc != UINT32_MAX) {
                            uint32_t ids2[2] = { A->id, vc };
                            osprey_factor_add(ctx, OSPREY_RULE_CB04, 1, false,
                                       P_UP, ids2, 2);
                            kr_account(ctx, OSPREY_PRED_ARRAY,
                                       &a1l->region, 1, 0);
                        }
                    }
                    /* Array(a1h,a2h,s2) */
                    int64_t len2;
                    if (osprey_check_sub(a2h->offset, a1h->offset, &len2) &&
                        len2 >= s2) {
                        OspreyVarPayload pc2;
                        memset(&pc2, 0, sizeof(pc2));
                        pc2.segment.a1 = *a1h;
                        pc2.segment.a2 = *a2h;
                        pc2.segment.size = (uint64_t)s2;
                        uint32_t vc = osprey_intern_var(ctx, OSPREY_PRED_ARRAY,
                                                 &pc2);
                        if (vc != UINT32_MAX) {
                            uint32_t ids2[2] = { B->id, vc };
                            osprey_factor_add(ctx, OSPREY_RULE_CB04, 1, false,
                                       P_UP, ids2, 2);
                            kr_account(ctx, OSPREY_PRED_ARRAY,
                                       &a1l->region, 1, 0);
                        }
                    }
                }
            }
        }
    }
}

/* CB05: scalar inside an array interval. */
static void cb05_scalars(OspreyContext *ctx, GArray *arrays, GArray *scalars)
{
    for (guint i = 0; i < arrays->len; i++) {
        OspreyVar *A = &g_array_index(arrays, OspreyVar, i);
        const OspreyAddress *a1, *a2;
        int64_t s;
        if (!array_interval(A, &a1, &a2, &s)) continue;
        for (guint j = 0; j < scalars->len; j++) {
            OspreyVar *S = &g_array_index(scalars, OspreyVar, j);
            int64_t v_off = S->payload.chunk.address.offset;
            int64_t v_end = v_off + (int64_t)S->payload.chunk.size;
            if (v_off < a1->offset || v_off >= a2->offset) continue;
            if (!same_region(&S->payload.chunk.address.region,
                             &a1->region)) continue;
            uint32_t ids[2] = { A->id, S->id };
            /* CB05: Scalar(v) ↔p↓ Array */
            osprey_factor_add(ctx, OSPREY_RULE_CB05, 0, true, P_DN, ids, 2);
            osprey_factor_add(ctx, OSPREY_RULE_CB05, 1, true, P_DN, ids, 2);
            if (!kr_has_space(ctx, OSPREY_PRED_ARRAY, &a1->region)) {
                kr_account(ctx, OSPREY_PRED_ARRAY, &a1->region, 0, 1);
                continue;
            }
            /* Array(a1, v.a, s) */
            if (v_off - a1->offset >= s) {
                OspreyVarPayload pc;
                memset(&pc, 0, sizeof(pc));
                pc.segment.a1 = *a1;
                pc.segment.a2 = S->payload.chunk.address;
                pc.segment.size = (uint64_t)s;
                uint32_t vc = osprey_intern_var(ctx, OSPREY_PRED_ARRAY, &pc);
                if (vc != UINT32_MAX) {
                    uint32_t ids3[3] = { A->id, S->id, vc };
                    osprey_factor_add(ctx, OSPREY_RULE_CB05, 2, false, P_UP, ids3, 3);
                    kr_account(ctx, OSPREY_PRED_ARRAY, &a1->region, 1, 0);
                }
            }
            /* Array(v.a+v.s, a2, s) */
            if (a2->offset - v_end >= s) {
                OspreyAddress a2l = S->payload.chunk.address;
                a2l.offset = v_end;
                OspreyVarPayload pb;
                memset(&pb, 0, sizeof(pb));
                pb.segment.a1 = a2l;
                pb.segment.a2 = *a2;
                pb.segment.size = (uint64_t)s;
                uint32_t vc = osprey_intern_var(ctx, OSPREY_PRED_ARRAY, &pb);
                if (vc != UINT32_MAX) {
                    uint32_t ids3[3] = { A->id, S->id, vc };
                    osprey_factor_add(ctx, OSPREY_RULE_CB05, 3, false, P_UP, ids3, 3);
                    kr_account(ctx, OSPREY_PRED_ARRAY, &a1->region, 1, 0);
                }
            }
        }
    }
}

/* CB07/CB08: ArrayStart support from BaseAddr / most-frequent access. */
static void cb07_cb08(OspreyContext *ctx)
{
    GHashTable *seen = g_hash_table_new_full(osprey_key_hash,
                                             osprey_key_equal,
                                             osprey_key_free, NULL);
    /* CB07: BaseAddr(i,v,a) ∧ AccessMultiChunks(i,v.a.r) */
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        OspreyBaseFact *b = &g_array_index(ctx->base_facts, OspreyBaseFact, i);
        /* multi-chunk check for (pc, region) */
        uint32_t distinct = 0;
        for (guint j = 0; j < ctx->access_facts->len; j++) {
            OspreyAccessFact *c = &g_array_index(ctx->access_facts,
                                                 OspreyAccessFact, j);
            if (c->pc != b->pc) continue;
            if (!same_region(&c->chunk.address.region,
                             &b->chunk.address.region)) continue;
            distinct++;
            if (distinct > 1) break;
        }
        if (distinct <= 1) continue;
        OspreyVarPayload pa, ps;
        memset(&pa, 0, sizeof(pa));
        pa.prim_access.chunk = b->chunk;
        pa.prim_access.insn_pc = b->pc;
        uint32_t v = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_ACCESS, &pa);
        if (v == UINT32_MAX) continue;
        memset(&ps, 0, sizeof(ps));
        ps.addr = b->base;
        uint32_t vs = osprey_intern_var(ctx, OSPREY_PRED_ARRAY_START, &ps);
        if (vs == UINT32_MAX) continue;
        uint32_t ids[2] = { v, vs };
        osprey_factor_add(ctx, OSPREY_RULE_CB07, 1, false, P_UP, ids, 2);
    }
    /* CB08: MostFreqAddrAccessed(i,r,v.a,k) ∧ AccessMultiChunks */
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *a = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        /* pick per (pc, region) only once; find most-frequent chunk */
        /* (use the max dynamic_count chunk among same (pc,region)) */
        uint32_t distinct = 0;
        const OspreyAccessFact *best = NULL;
        uint64_t best_cnt = 0;
        for (guint j = 0; j < ctx->access_facts->len; j++) {
            OspreyAccessFact *b = &g_array_index(ctx->access_facts,
                                                 OspreyAccessFact, j);
            if (b->pc != a->pc) continue;
            if (!same_region(&b->chunk.address.region,
                             &a->chunk.address.region)) continue;
            distinct++;
            if (distinct == 1) {
                best = b;
                best_cnt = b->dynamic_count;
            } else if (b->dynamic_count > best_cnt) {
                best = b;
                best_cnt = b->dynamic_count;
            }
        }
        if (distinct <= 1 || best == NULL) continue;
        OspreyKey seen_key = osprey_pc_region_key(
            best->pc, &best->chunk.address.region);
        if (g_hash_table_lookup(seen, &seen_key) != NULL)
            continue;
        g_hash_table_insert(seen, osprey_key_new(&seen_key),
                            GSIZE_TO_POINTER(1));
        OspreyVarPayload pa, ps;
        memset(&pa, 0, sizeof(pa));
        pa.prim_access.chunk = best->chunk;
        pa.prim_access.insn_pc = best->pc;
        uint32_t v = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_ACCESS, &pa);
        if (v == UINT32_MAX) continue;
        memset(&ps, 0, sizeof(ps));
        ps.addr = best->chunk.address;
        uint32_t vs = osprey_intern_var(ctx, OSPREY_PRED_ARRAY_START, &ps);
        if (vs == UINT32_MAX) continue;
        double pk = support_ratio(ctx, best->sample_support);
        uint32_t ids[2] = { v, vs };
        osprey_factor_add(ctx, OSPREY_RULE_CB08, 1, false, pk, ids, 2);
    }
    g_hash_table_destroy(seen);
}

/* CC04/CC05: UnfoldableHeap pairwise (exclusion / monotonic support). */
static void cc04_cc05(OspreyContext *ctx)
{
    OspreyGraph *g = ctx->graph;
    for (guint i = 0; i < g->vars->len; i++) {
        OspreyVar *u1 = &g_array_index(g->vars, OspreyVar, i);
        if (u1->kind != OSPREY_PRED_UNFOLDABLE_HEAP) continue;
        for (guint j = i + 1; j < g->vars->len; j++) {
            OspreyVar *u2 = &g_array_index(g->vars, OspreyVar, j);
            if (u2->kind != OSPREY_PRED_UNFOLDABLE_HEAP) continue;
            if (!same_region(&u1->payload.heap_fold.region,
                             &u2->payload.heap_fold.region)) continue;
            uint64_t s1 = u1->payload.heap_fold.size;
            uint64_t s2 = u2->payload.heap_fold.size;
            if (s1 != s2) {
                /* CC04: exclusion */
                uint32_t ids[2] = { u1->id, u2->id };
                osprey_factor_add(ctx, OSPREY_RULE_CC04, 0, true, P_DN, ids, 2);
                osprey_factor_add(ctx, OSPREY_RULE_CC04, 1, true, P_DN, ids, 2);
            } else if (s1 < s2) {
                /* CC05: s1 <= s2 support */
                uint32_t ids[2] = { u1->id, u2->id };
                osprey_factor_add(ctx, OSPREY_RULE_CC05, 1, false, P_UP, ids, 2);
            }
        }
    }
}

/* CD07: PrimitiveVar(v) in heap H_i -> FieldOf(v, <H_i,0>). */
static void cd07_heap_fields(OspreyContext *ctx)
{
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *a = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        if (a->chunk.address.region.kind != OSPREY_REGION_HEAP_SITE)
            continue;
        OspreyVarPayload pv;
        memset(&pv, 0, sizeof(pv));
        pv.chunk = a->chunk;
        uint32_t v = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pv);
        if (v == UINT32_MAX) continue;
        OspreyVarPayload pf;
        memset(&pf, 0, sizeof(pf));
        pf.attached.chunk = a->chunk;
        pf.attached.base.region = a->chunk.address.region;
        pf.attached.base.offset = 0;
        uint32_t f = osprey_intern_var(ctx, OSPREY_PRED_FIELD_OF, &pf);
        if (f == UINT32_MAX) continue;
        uint32_t ids[2] = { v, f };
        osprey_factor_add(ctx, OSPREY_RULE_CD07, 1, false, P_UP, ids, 2);
    }
}

/* CD08: FieldOf(v1,a1) ∧ HomoSegment(a1,a2,s) -> FieldOf(v2,a2) for
 * v1.a=a1+n, v2.a=a2+n, 1<=n<=s.  Creates v2 FieldOf candidates
 * (bounded per region). */
static void cd08_fields(OspreyContext *ctx)
{
    OspreyGraph *g = ctx->graph;
    GArray *homos = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    GArray *fields = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    for (guint i = 0; i < g->vars->len; i++) {
        OspreyVar *v = &g_array_index(g->vars, OspreyVar, i);
        if (v->kind == OSPREY_PRED_HOMO_SEGMENT) {
            uint32_t id = v->id;
            g_array_append_val(homos, id);
        } else if (v->kind == OSPREY_PRED_FIELD_OF) {
            uint32_t id = v->id;
            g_array_append_val(fields, id);
        }
    }
    for (guint hi = 0; hi < homos->len; hi++) {
        uint32_t hid = g_array_index(homos, uint32_t, hi);
        OspreyVar *h = &g_array_index(g->vars, OspreyVar, hid);
        const OspreyAddress *a1 = &h->payload.segment.a1;
        const OspreyAddress *a2 = &h->payload.segment.a2;
        int64_t s = h->payload.segment.size;
        if (s <= 0) continue;
        for (guint fi = 0; fi < fields->len; fi++) {
            uint32_t fid = g_array_index(fields, uint32_t, fi);
            OspreyVar *f1 = &g_array_index(g->vars, OspreyVar, fid);
            const OspreyChunk *c1 = &f1->payload.attached.chunk;
            int64_t n;
            if (!osprey_check_sub(c1->address.offset, a1->offset, &n))
                continue;
            if (!(n >= 1 && n <= s)) continue;
            if (!same_region(&c1->address.region, &a1->region)) continue;
            /* partner chunk at a2 + n, same size */
            if (!kr_has_space(ctx, OSPREY_PRED_FIELD_OF, &a2->region)) {
                kr_account(ctx, OSPREY_PRED_FIELD_OF, &a2->region, 0, 1);
                continue;
            }
            OspreyChunk c2 = *c1;
            c2.address.region = a2->region;
            int64_t off2;
            if (!osprey_check_add(a2->offset, n, &off2)) continue;
            c2.address.offset = off2;
            OspreyVarPayload pf;
            memset(&pf, 0, sizeof(pf));
            pf.attached.chunk = c2;
            pf.attached.base = *a2;
            uint32_t f2 = osprey_intern_var(ctx, OSPREY_PRED_FIELD_OF, &pf);
            if (f2 == UINT32_MAX) continue;
            kr_account(ctx, OSPREY_PRED_FIELD_OF, &a2->region, 1, 0);
            uint32_t ids[3] = { fid, hid, f2 };
            osprey_factor_add(ctx, OSPREY_RULE_CD08, 2, false, P_UP, ids, 3);
        }
    }
    g_array_free(homos, TRUE);
    g_array_free(fields, TRUE);
}

/* CB06: hard-false for invalid array intervals (hi-lo < stride). */
static void cb06_hard_false(OspreyContext *ctx)
{
    OspreyGraph *g = ctx->graph;
    for (guint i = 0; i < g->vars->len; i++) {
        OspreyVar *v = &g_array_index(g->vars, OspreyVar, i);
        if (v->kind != OSPREY_PRED_ARRAY) continue;
        const OspreyAddress *lo, *hi;
        int64_t s;
        if (!array_interval(v, &lo, &hi, &s)) continue;
        int64_t len;
        if (!osprey_check_sub(hi->offset, lo->offset, &len)) continue;
        if (len < s) {
            v->hard_false = 1;
        }
    }
}

/* Stage-3 secondary entry: instantiate remaining deterministic rules
 * (no beliefs needed; CC07 folding comes after the first BP pass). */
OspreyStatus osprey_stage3_secondary(OspreyContext *ctx)
{
    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    if (ctx->graph == NULL) return OSPREY_INCOMPLETE_FACTS;

    /* CB02 first (creates Array vars), then interval-pair rules */
    secondary_cb02(ctx);

    /* bucket arrays + scalars per region */
    GHashTable *array_buckets = bucket_new();
    GHashTable *scalar_buckets = bucket_new();
    {
        OspreyGraph *g = ctx->graph;
        for (guint i = 0; i < g->vars->len; i++) {
            OspreyVar *v = &g_array_index(g->vars, OspreyVar, i);
            if (v->kind == OSPREY_PRED_ARRAY) {
                bucket_add(array_buckets, &v->payload.segment.a1.region, v->id);
            } else if (v->kind == OSPREY_PRED_SCALAR) {
                bucket_add(scalar_buckets, &v->payload.chunk.address.region,
                           v->id);
            }
        }
    }
    /* per-region pair processing */
    GHashTableIter bit;
    gpointer rk, arr_ptr;
    g_hash_table_iter_init(&bit, array_buckets);
    while (g_hash_table_iter_next(&bit, &rk, &arr_ptr)) {
        GArray *arrays = (GArray *)arr_ptr;
        cb03_cb04_pairs(ctx, arrays);
    }
    g_hash_table_iter_init(&bit, scalar_buckets);
    while (g_hash_table_iter_next(&bit, &rk, &arr_ptr)) {
        /* The bucket key is the full region identity (struct key);
         * decode it back to a region id for the cross-bucket lookup. */
        const OspreyKey *rkp = rk;
        OspreyRegionId r0;
        r0.kind = (OspreyRegionKind)rkp->w[0];
        r0.code_image_id = rkp->w[1];
        r0.site_offset = rkp->w[2];
        GArray *scalars = (GArray *)arr_ptr;
        GArray *arrays = NULL;
        bucket_region_arrays(array_buckets, &r0, &arrays);
        if (arrays != NULL) {
            cb05_scalars(ctx, arrays, scalars);
        }
    }

    cb07_cb08(ctx);
    cc04_cc05(ctx);
    cd07_heap_fields(ctx);
    cd08_fields(ctx);
    cb06_hard_false(ctx);

    g_hash_table_destroy(array_buckets);
    g_hash_table_destroy(scalar_buckets);

    /* Propagate any limit/error status set during secondary
     * instantiation (fail-closed transaction). */
    if (ctx->last_status != OSPREY_OK) {
        return ctx->last_status;
    }
    OspreyGraph *g = ctx->graph;
    log_msg("[osprey] [graph] [stage secondary] [vars %u] [factors %u]\n",
            g->vars->len, g->factors->len);
    return OSPREY_OK;
}

/* ------------------------------------------------------------------ */
/* Stage-3 base entry                                                  */
/* ------------------------------------------------------------------ */

OspreyStatus osprey_stage3_base(OspreyContext *ctx) {
    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    if (ctx->relations == NULL) {
        OspreyStatus relation_status = osprey_relations_build(ctx);
        if (relation_status != OSPREY_OK) {
            osprey_tx_reject(ctx, relation_status, "relations",
                             "checked relation arithmetic failed");
            return relation_status;
        }
    }
    if (ctx->graph == NULL) {
        ctx->graph = osprey_graph_new();
    }
    OspreyGraph *g = ctx->graph;

    /* R10-R12 hint extraction (deterministic closure) */
    closure_r10(ctx);
    closure_r11(ctx);
    closure_r12(ctx);

    /* static factor instantiation (base rules) */
    instantiate_ca01(ctx);
    instantiate_ca02_ca03(ctx);
    instantiate_ca04_ca05(ctx);
    instantiate_ca06(ctx);
    instantiate_ca07(ctx);
    instantiate_cb01(ctx);
    instantiate_cc01_cc02(ctx);
    instantiate_cc03(ctx);
    instantiate_cd01_03(ctx);
    instantiate_cd06(ctx);
    instantiate_cd11(ctx);

    /* CD04 HomoSegment closure from hints (bounded) */
    closure_cd04(ctx);

    /* CD10 exclusion after all FieldOf vars exist */
    instantiate_cd10(ctx);

    /* distinct union-find roots over interned vars */
    uint32_t components = 0;
    GHashTable *roots = g_hash_table_new(g_direct_hash, g_direct_equal);
    for (uint32_t i = 0; i < g->vars->len; i++) {
        uint32_t r = uf_find(g, i);
        if (g_hash_table_lookup(roots, GSIZE_TO_POINTER(r)) == NULL) {
            g_hash_table_insert(roots, GSIZE_TO_POINTER(r), GSIZE_TO_POINTER(1));
            components++;
        }
    }
    g_hash_table_destroy(roots);

    /* Propagate any limit/error status set during interning or factor
     * instantiation (fail-closed transaction). */
    if (ctx->last_status != OSPREY_OK) {
        return ctx->last_status;
    }
    log_msg("[osprey] [graph] [stage base] [vars %u] [factors %u] "
            "[components %u] [hints %llu] [cd04 %llu]\n",
            g->vars->len, g->factors->len, components,
            (unsigned long long)g->hint_instances,
            (unsigned long long)g->cd04_extensions);
    return OSPREY_OK;
}
