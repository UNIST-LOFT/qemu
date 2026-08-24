/*
 * OSPREY Stage-3 inference: exact component solving, log-domain loopy
 * belief propagation, and dynamic CC07 heap-folding closure.
 *
 * Plan (OSPREY_IMPLEMENTATION.md §8):
 *  - Partition variables/factors into connected components (union-find
 *    edges established at instantiation).
 *  - Solve each component with size <= min(max_exact_clique_vars, 16)
 *    exactly by full joint enumeration; larger components start at
 *    uniform beliefs.
 *  - Log-domain loopy BP over the full graph, seeded from exact
 *    beliefs; damping 0.5, tolerance 1e-6 for 10 consecutive rounds,
 *    hard cap 500 rounds; retain best damped iterate on failure.
 *  - CC07: heap chunks at offset >= s_h+s_t fold onto
 *    (o - s_h) mod s_t + s_h once UnfoldableHeap(i,s_h) and
 *    FoldableHeap(i,s_t) clear 0.5 with s_t > 0; folded primitives get
 *    CA01/CC03 stage-2 factors and CC07 implications; BP reruns until
 *    no new variables (metadata: [osprey] [infer] rows).
 *
 * Generic factor potential (§7.1): weight p everywhere except the
 * penalized assignment (all antecedents true, head violates the
 * implication direction), which gets 1-p.  Unary factors (head_idx ==
 * UINT16_MAX) are priors: p on the preferred truth value.  CB06
 * hard-false pins Array beliefs at zero.
 */

#include "osprey.h"
#include "osprey-internal.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>

/* Diagnostic sink (snapshot.c). */
void log_msg(const char *fmt, ...);

#define OSPREY_BP_MAX_ITERS 500u
#define OSPREY_BP_TOL 1e-6
#define OSPREY_BP_CONVERGED_ROUNDS 10u
#define OSPREY_BP_DAMPING 0.5
#define OSPREY_BP_MAX_FOLD_ROUNDS 8u
#define OSPREY_EXACT_MAX_VARS 16u
#define OSPREY_P_UP 0.8
#define OSPREY_P_DN 0.2

/* ------------------------------------------------------------------ */
/* Region helpers                                                      */
/* ------------------------------------------------------------------ */

static bool region_eq(const OspreyRegionId *a, const OspreyRegionId *b) {
    return a->kind == b->kind && a->code_image_id == b->code_image_id &&
           a->site_offset == b->site_offset;
}

/* ------------------------------------------------------------------ */
/* Factor potential (§7.1)                                             */
/* ------------------------------------------------------------------ */

static double factor_value(const OspreyFactor *f, const uint32_t *bits) {
    if (f->head_idx == UINT16_MAX) {
        bool on = bits[0] != 0;
        if (f->negative) {
            return on ? 1.0 - f->p : f->p;
        }
        return on ? f->p : 1.0 - f->p;
    }
    uint32_t head = bits[f->head_idx];
    bool antecedents = true;
    for (uint32_t i = 0; i < f->num_vars; i++) {
        if (i == f->head_idx) continue;
        if (bits[i] == 0) { antecedents = false; break; }
    }
    bool violated;
    if (!antecedents) {
        violated = false;
    } else if (f->negative) {
        violated = (head != 0);
    } else {
        violated = (head == 0);
    }
    return violated ? 1.0 - f->p : f->p;
}

/* ------------------------------------------------------------------ */
/* Component partition                                                 */
/* ------------------------------------------------------------------ */

static uint32_t uf_find(OspreyGraph *g, uint32_t x) {
    while (g->uf_parent[x] != x) {
        g->uf_parent[x] = g->uf_parent[g->uf_parent[x]];
        x = g->uf_parent[x];
    }
    return x;
}

static void bucket_free(gpointer p) {
    g_array_free((GArray *)p, TRUE);
}

/* Root -> GArray(uint32 var ids). */
static GHashTable *component_buckets(OspreyGraph *g) {
    GHashTable *b = g_hash_table_new_full(g_direct_hash, g_direct_equal,
                                          NULL, bucket_free);
    for (uint32_t i = 0; i < g->vars->len; i++) {
        uint32_t r = uf_find(g, i);
        GArray *arr = g_hash_table_lookup(b, GSIZE_TO_POINTER(r));
        if (arr == NULL) {
            arr = g_array_new(FALSE, FALSE, sizeof(uint32_t));
            g_hash_table_insert(b, GSIZE_TO_POINTER(r), arr);
        }
        uint32_t id = i;
        g_array_append_val(arr, id);
    }
    return b;
}

/* ------------------------------------------------------------------ */
/* Exact component solve (joint enumeration)                           */
/* ------------------------------------------------------------------ */

static bool exact_solve_component(OspreyContext *ctx, const uint32_t *comp,
                                  uint32_t m) {
    OspreyGraph *g = ctx->graph;
    if (m == 0 || m > OSPREY_EXACT_MAX_VARS) return false;
    uint32_t total = 1u << m;
    uint32_t *pos = g_new(uint32_t, g->vars->len);
    for (uint32_t i = 0; i < m; i++) pos[comp[i]] = i;
    double *joint = g_new(double, total);
    for (uint32_t a = 0; a < total; a++) {
        double v = 1.0;
        for (guint fi = 0; fi < g->factors->len; fi++) {
            OspreyFactor *f = g_array_index(g->factors, OspreyFactor *, fi);
            uint32_t bits[16];
            bool inside = true;
            for (uint32_t i = 0; i < f->num_vars; i++) {
                uint32_t var = f->var_ids[i];
                if (var >= g->vars->len || pos[var] >= m) {
                    inside = false;
                    break;
                }
                bits[i] = (a >> pos[var]) & 1;
            }
            if (!inside) continue;
            v *= factor_value(f, bits);
        }
        joint[a] = v;
    }
    double z = 0.0;
    for (uint32_t a = 0; a < total; a++) z += joint[a];
    for (uint32_t i = 0; i < m; i++) {
        double s1 = 0.0;
        for (uint32_t a = 0; a < total; a++) {
            if ((a >> i) & 1) s1 += joint[a];
        }
        g_array_index(g->vars, OspreyVar, comp[i]).belief =
            (z > 0.0) ? s1 / z : 0.5;
    }
    g_free(joint);
    g_free(pos);
    return true;
}

static uint32_t exact_pass(OspreyContext *ctx) {
    OspreyGraph *g = ctx->graph;
    GHashTable *buckets = component_buckets(g);
    uint32_t exact_comps = 0, large_comps = 0, solved_vars = 0;
    GHashTableIter it;
    gpointer rk, arr_ptr;
    g_hash_table_iter_init(&it, buckets);
    while (g_hash_table_iter_next(&it, &rk, &arr_ptr)) {
        GArray *arr = (GArray *)arr_ptr;
        uint32_t m = arr->len;
        uint32_t cap = ctx->config.max_exact_clique_vars;
        if (cap > OSPREY_EXACT_MAX_VARS) cap = OSPREY_EXACT_MAX_VARS;
        if (m > cap) {
            large_comps++;
            continue;
        }
        if (exact_solve_component(ctx, (uint32_t *)arr->data, m)) {
            exact_comps++;
            solved_vars += m;
        }
    }
    g_hash_table_destroy(buckets);
    log_msg("[osprey] [infer] [exact] [components %u] [vars %u] "
            "[large %u]\n", exact_comps, solved_vars, large_comps);
    return exact_comps;
}

/* ------------------------------------------------------------------ */
/* Loopy BP (log domain, synchronous, damped)                          */
/* ------------------------------------------------------------------ */

typedef struct OspEdge {
    uint32_t factor;      /* index into graph->factors */
    uint32_t var;         /* var id */
    uint32_t pos;         /* position of var within factor->var_ids */
    uint32_t next;        /* next edge id in the same ring */
} OspEdge;

typedef struct OspBp {
    OspreyGraph *g;
    GArray *edges;        /* OspEdge */
    uint32_t *var_ring;   /* var id -> head edge id (UINT32_MAX none) */
    uint32_t *fac_ring;   /* factor idx -> head edge id */
    double *msg_fv0, *msg_fv1;   /* factor -> variable log messages */
    double *msg_vf0, *msg_vf1;   /* variable -> factor log messages */
} OspBp;

static void bp_build(OspBp *bp, OspreyGraph *g) {
    memset(bp, 0, sizeof(*bp));
    bp->g = g;
    bp->edges = g_array_new(FALSE, FALSE, sizeof(OspEdge));
    bp->fac_ring = g_new(uint32_t, g->factors->len);
    bp->var_ring = g_new(uint32_t, g->vars->len);
    for (uint32_t f = 0; f < g->factors->len; f++) bp->fac_ring[f] = UINT32_MAX;
    for (uint32_t v = 0; v < g->vars->len; v++) bp->var_ring[v] = UINT32_MAX;
    for (guint fi = 0; fi < g->factors->len; fi++) {
        OspreyFactor *F = g_array_index(g->factors, OspreyFactor *, fi);
        for (uint32_t i = 0; i < F->num_vars; i++) {
            OspEdge e;
            e.factor = fi;
            e.var = F->var_ids[i];
            e.pos = i;
            e.next = bp->fac_ring[fi];
            g_array_append_val(bp->edges, e);
            bp->fac_ring[fi] = bp->edges->len - 1;
        }
    }
    for (guint i = 0; i < bp->edges->len; i++) {
        OspEdge *e = &g_array_index(bp->edges, OspEdge, i);
        e->next = bp->var_ring[e->var];
        bp->var_ring[e->var] = i;
    }
    uint32_t n = bp->edges->len;
    bp->msg_fv0 = g_new0(double, n);
    bp->msg_fv1 = g_new0(double, n);
    bp->msg_vf0 = g_new(double, n);
    bp->msg_vf1 = g_new(double, n);
    /* seed variable->factor messages from exact beliefs */
    for (uint32_t i = 0; i < n; i++) {
        OspEdge *e = &g_array_index(bp->edges, OspEdge, i);
        double b = g_array_index(g->vars, OspreyVar, e->var).belief;
        if (!(b > 0.0)) b = 0.5;
        if (b > 0.999999) b = 0.999999;
        if (b < 0.000001) b = 0.000001;
        bp->msg_vf0[i] = log(1.0 - b);
        bp->msg_vf1[i] = log(b);
    }
}

static void bp_free(OspBp *bp) {
    g_array_free(bp->edges, TRUE);
    g_free(bp->fac_ring);
    g_free(bp->var_ring);
    g_free(bp->msg_fv0);
    g_free(bp->msg_fv1);
    g_free(bp->msg_vf0);
    g_free(bp->msg_vf1);
}

/* Variable -> factor: sum of incoming factor logs. */
static void bp_var_to_factor(OspBp *bp, uint32_t edge) {
    OspEdge *e = &g_array_index(bp->edges, OspEdge, edge);
    double l0 = 0.0, l1 = 0.0;
    uint32_t ring = bp->var_ring[e->var];
    while (ring != UINT32_MAX) {
        if (ring != edge) {
            l0 += bp->msg_fv0[ring];
            l1 += bp->msg_fv1[ring];
        }
        ring = g_array_index(bp->edges, OspEdge, ring).next;
    }
    bp->msg_vf0[edge] = l0;
    bp->msg_vf1[edge] = l1;
}

/* Factor -> variable: eliminate the factor's other variables over its
 * table (k <= 8 by the factor-add cap). */
static void bp_factor_to_var(OspBp *bp, uint32_t edge) {
    OspEdge *e = &g_array_index(bp->edges, OspEdge, edge);
    OspreyFactor *f = g_array_index(bp->g->factors, OspreyFactor *,
                                    e->factor);
    uint32_t k = f->num_vars;
    uint32_t total = 1u << k;
    double in0[8], in1[8];
    for (uint32_t i = 0; i < k; i++) {
        in0[i] = in1[i] = 0.0;
        uint32_t ring = bp->fac_ring[e->factor];
        while (ring != UINT32_MAX) {
            OspEdge *o = &g_array_index(bp->edges, OspEdge, ring);
            if (o->pos == i) {
                in0[i] = bp->msg_vf0[ring];
                in1[i] = bp->msg_vf1[ring];
                break;
            }
            ring = o->next;
        }
    }
    double m0 = -INFINITY, m1 = -INFINITY;
    uint32_t bits[8];
    for (uint32_t a = 0; a < total; a++) {
        if (((a >> e->pos) & 1) != 0) continue;
        for (uint32_t i = 0; i < k; i++) bits[i] = (a >> i) & 1;
        double l = log(factor_value(f, bits));
        for (uint32_t i = 0; i < k; i++) l += (bits[i] ? in1[i] : in0[i]);
        if (l > m0) m0 = l;
    }
    for (uint32_t a = 0; a < total; a++) {
        if (((a >> e->pos) & 1) == 0) continue;
        for (uint32_t i = 0; i < k; i++) bits[i] = (a >> i) & 1;
        double l = log(factor_value(f, bits));
        for (uint32_t i = 0; i < k; i++) l += (bits[i] ? in1[i] : in0[i]);
        if (l > m1) m1 = l;
    }
    bp->msg_fv0[edge] = m0;
    bp->msg_fv1[edge] = m1;
}

static void bp_round(OspBp *bp) {
    for (guint i = 0; i < bp->edges->len; i++) bp_var_to_factor(bp, i);
    for (guint i = 0; i < bp->edges->len; i++) bp_factor_to_var(bp, i);
}

static double bp_belief(OspBp *bp, uint32_t var) {
    OspreyVar *v = &g_array_index(bp->g->vars, OspreyVar, var);
    if (v->hard_false) return 0.0;
    double l0 = 0.0, l1 = 0.0;
    uint32_t ring = bp->var_ring[var];
    while (ring != UINT32_MAX) {
        l0 += bp->msg_fv0[ring];
        l1 += bp->msg_fv1[ring];
        ring = g_array_index(bp->edges, OspEdge, ring).next;
    }
    double mx = l0 > l1 ? l0 : l1;
    double e0 = exp(l0 - mx), e1 = exp(l1 - mx);
    double s = e0 + e1;
    if (!(s > 0.0)) return 0.5;
    return e1 / s;
}

/* Damped synchronous BP; writes beliefs; returns (iters, converged). */
static bool bp_run(OspBp *bp, uint32_t max_iters, uint32_t *iters_out,
                   double *best_delta_out) {
    OspreyGraph *g = bp->g;
    double *prev = g_new(double, g->vars->len);
    for (uint32_t i = 0; i < g->vars->len; i++) {
        prev[i] = g_array_index(g->vars, OspreyVar, i).belief;
        if (!(prev[i] > 0.0)) prev[i] = 0.5;
    }
    double best_delta = INFINITY;
    uint32_t stable = 0;
    uint32_t iters = 0;
    bool converged = false;
    for (uint32_t it = 0; it < max_iters; it++) {
        iters = it + 1;
        bp_round(bp);
        /* damping: blend new messages with the previous iterate */
        double *old0 = g_new(double, bp->edges->len);
        double *old1 = g_new(double, bp->edges->len);
        memcpy(old0, bp->msg_fv0, bp->edges->len * sizeof(double));
        memcpy(old1, bp->msg_fv1, bp->edges->len * sizeof(double));
        for (guint i = 0; i < bp->edges->len; i++) {
            bp->msg_fv0[i] = OSPREY_BP_DAMPING * old0[i] +
                             (1.0 - OSPREY_BP_DAMPING) * bp->msg_fv0[i];
            bp->msg_fv1[i] = OSPREY_BP_DAMPING * old1[i] +
                             (1.0 - OSPREY_BP_DAMPING) * bp->msg_fv1[i];
        }
        g_free(old0);
        g_free(old1);
        double max_delta = 0.0;
        for (uint32_t v = 0; v < g->vars->len; v++) {
            double b = bp_belief(bp, v);
            g_array_index(g->vars, OspreyVar, v).belief = b;
            double d = fabs(b - prev[v]);
            if (d > max_delta) max_delta = d;
            prev[v] = b;
        }
        if (max_delta < best_delta) best_delta = max_delta;
        if (max_delta < OSPREY_BP_TOL) {
            stable++;
            if (stable >= OSPREY_BP_CONVERGED_ROUNDS) {
                converged = true;
                break;
            }
        } else {
            stable = 0;
        }
    }
    g_free(prev);
    *iters_out = iters;
    *best_delta_out = best_delta;
    return converged;
}

/* ------------------------------------------------------------------ */
/* CC07 heap folding closure                                           */
/* ------------------------------------------------------------------ */

static uint32_t cc07_fold_pass(OspreyContext *ctx) {
    OspreyGraph *g = ctx->graph;
    uint32_t created = 0;
    for (guint i = 0; i < g->vars->len; i++) {
        OspreyVar *u = &g_array_index(g->vars, OspreyVar, i);
        if (u->kind != OSPREY_PRED_UNFOLDABLE_HEAP) continue;
        if (u->belief <= 0.5) continue;
        uint64_t s_h = u->payload.heap_fold.size;
        for (guint j = 0; j < g->vars->len; j++) {
            OspreyVar *t = &g_array_index(g->vars, OspreyVar, j);
            if (t->kind != OSPREY_PRED_FOLDABLE_HEAP) continue;
            if (t->belief <= 0.5) continue;
            uint64_t s_t = t->payload.heap_fold.size;
            if (s_t == 0) continue;      /* CC07 guard */
            if (!region_eq(&u->payload.heap_fold.region,
                             &t->payload.heap_fold.region)) continue;
            int64_t tail_lo = (int64_t)(s_h + s_t);
            for (guint k = 0; k < g->vars->len; k++) {
                OspreyVar *v = &g_array_index(g->vars, OspreyVar, k);
                if (v->kind != OSPREY_PRED_PRIMITIVE_VAR) continue;
                const OspreyAddress *va = &v->payload.chunk.address;
                if (va->region.kind != OSPREY_REGION_HEAP_SITE) continue;
                if (!region_eq(&va->region,
                                 &u->payload.heap_fold.region)) continue;
                int64_t o = va->offset;
                if (o < tail_lo) continue;
                int64_t rel = o - (int64_t)s_h;
                int64_t mod = rel % (int64_t)s_t;
                int64_t fo = mod + (int64_t)s_h;
                if (fo == o) continue;
                OspreyChunk fc = v->payload.chunk;
                fc.address.offset = fo;
                OspreyVarPayload pv;
                memset(&pv, 0, sizeof(pv));
                pv.chunk = fc;
                uint32_t nv = osprey_intern_var(ctx,
                                                OSPREY_PRED_PRIMITIVE_VAR,
                                                &pv);
                if (nv == UINT32_MAX) continue;
                bool is_new = (nv == g->vars->len - 1);
                if (is_new) created++;
                uint32_t ids3[3] = { v->id, u->id, t->id };
                osprey_factor_add(ctx, OSPREY_RULE_CC07, 0, false,
                                  OSPREY_P_UP, ids3, 3);
                uint32_t ids2[2] = { nv, v->id };
                osprey_factor_add(ctx, OSPREY_RULE_CC07, 1, true,
                                  OSPREY_P_DN, ids2, 2);
            }
        }
    }
    return created;
}

/* ------------------------------------------------------------------ */
/* Stage-3 entry                                                       */
/* ------------------------------------------------------------------ */

OspreyStatus osprey_infer(OspreyContext *ctx) {
    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    if (ctx->graph == NULL || ctx->graph->vars->len == 0) {
        return OSPREY_INCOMPLETE_FACTS;
    }
    OspreyGraph *g = ctx->graph;

    /* 1. exact component solving */
    exact_pass(ctx);

    /* 2. loopy BP with folding closure */
    uint32_t fold_rounds = 0;
    bool converged = false;
    uint32_t iters = 0;
    double best_delta = INFINITY;
    for (;;) {
        OspBp bp;
        bp_build(&bp, g);
        converged = bp_run(&bp, OSPREY_BP_MAX_ITERS, &iters, &best_delta);
        bp_free(&bp);
        if (fold_rounds >= OSPREY_BP_MAX_FOLD_ROUNDS) break;
        uint32_t created = cc07_fold_pass(ctx);
        if (created == 0) break;
        fold_rounds++;
        log_msg("[osprey] [fold] [round %u] [new-vars %u]\n",
                fold_rounds, created);
    }

    uint32_t above = 0;
    for (uint32_t v = 0; v < g->vars->len; v++) {
        OspreyVar *var = &g_array_index(g->vars, OspreyVar, v);
        if (var->belief > 0.5) above++;
    }
    log_msg("[osprey] [infer] [bp] [iters %u] [converged %d] "
            "[best-delta %.3g] [belief>0.5 %u] [fold-rounds %u]\n",
            iters, converged ? 1 : 0, best_delta, above, fold_rounds);

    ctx->last_status = converged ? OSPREY_OK : OSPREY_NON_CONVERGED;
    return ctx->last_status;
}
