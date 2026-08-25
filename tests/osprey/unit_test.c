/*
 * OSPREY Stage-0 fail-closed transaction unit tests.
 *
 * Links the five OSPREY translation units (osprey.o, osprey-facts.o,
 * osprey-rules.o, osprey-infer.o, osprey-decode.o) from the tracer
 * build against a small stub environment (log_msg, is_valid_address,
 * guest_base, qemu mutex primitives) and drives the public API:
 *
 *  - merge validation rejects overflow / bad arithmetic / unsupported
 *    execution / version or capacity mismatch / malformed population /
 *    used>cap before appending any committed fact;
 *  - a rejected merge leaves the transaction non-OK, emits exactly one
 *    [osprey] [reject] row, and exposes no model;
 *  - osprey_analyze() stages the graph/model and installs them only on
 *    OSPREY_OK; variable/factor/decoder/exact-component caps and
 *    empty-graph incomplete facts reject the transaction;
 *  - a later rejected transaction hides the previously committed model
 *    from consumers (osprey_model() == NULL) while retaining it
 *    internally until the next successful transaction;
 *  - a fresh baseline transaction recovers from a previous rejection.
 *
 * Build: see tests/osprey/Makefile (target `unit`).
 */

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ucontext.h>

#include "osprey.h"
#include "osprey-internal.h"
#include "qemu/thread.h"

/* ------------------------------------------------------------------ */
/* Stub environment                                                    */
/* ------------------------------------------------------------------ */

unsigned long guest_base = 0;

static char g_test_log[1 << 20];
static size_t g_test_log_len = 0;
static int g_reject_rows = 0;

void log_msg(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    int n = vsnprintf(g_test_log + g_test_log_len,
                      sizeof(g_test_log) - g_test_log_len, fmt, ap);
    va_end(ap);
    if (n > 0) {
        if (strstr(g_test_log + g_test_log_len, "[reject]") != NULL) {
            g_reject_rows++;
        }
        g_test_log_len += (size_t)n;
        if (g_test_log_len > sizeof(g_test_log) - 1) {
            g_test_log_len = sizeof(g_test_log) - 1;
        }
    }
}

bool is_valid_address(target_ulong addr, bool for_snapshot)
{
    (void)addr;
    (void)for_snapshot;
    return false;
}

void qemu_mutex_init(QemuMutex *m)
{
    pthread_mutex_init(&m->lock, NULL);
}

void qemu_mutex_destroy(QemuMutex *m)
{
    pthread_mutex_destroy(&m->lock);
}

void qemu_mutex_lock_impl(QemuMutex *m, const char *file, const int line)
{
    (void)file;
    (void)line;
    pthread_mutex_lock(&m->lock);
}

void qemu_mutex_unlock_impl(QemuMutex *m, const char *file, const int line)
{
    (void)file;
    (void)line;
    pthread_mutex_unlock(&m->lock);
}

QemuMutexLockFunc qemu_mutex_lock_func = qemu_mutex_lock_impl;
QemuMutexTrylockFunc qemu_mutex_trylock_func = NULL;

/* ------------------------------------------------------------------ */
/* Harness                                                             */
/* ------------------------------------------------------------------ */

static int failures = 0;

#define CHECK(cond, msg) do {                                            \
    if (!(cond)) {                                                       \
        fprintf(stderr, "FAIL: %s (line %d)\n", (msg), __LINE__);        \
        failures++;                                                      \
    }                                                                    \
} while (0)

static void reset_log(void)
{
    g_test_log_len = 0;
    g_reject_rows = 0;
    g_test_log[0] = '\0';
}

static OspreyConfig test_config(void)
{
    OspreyConfig c;
    memset(&c, 0, sizeof(c));
    c.enabled = true;
    c.shared_bytes = 1u << 20;
    c.max_facts = 262144;
    c.max_chunks_per_region = 8192;
    c.max_candidates_per_kind_region = 4096;
    c.max_variables = 100000;
    c.max_factors = 500000;
    c.max_exact_clique_vars = 20;
    c.report_threshold = 0.2;
    return c;
}

static OspreySharedRun *new_run(const OspreyConfig *c)
{
    size_t sz = osprey_shared_run_size(c);
    OspreySharedRun *run = g_malloc0(sz);
    osprey_shared_run_reset(run, 1, c);
    return run;
}

/* Two distinct 8-byte access facts: global region, offsets 0 and 8,
 * different PCs. */
static void fill_two_access_facts(OspreySharedRun *run)
{
    OspreyAccessFact f1, f2;
    memset(&f1, 0, sizeof(f1));
    f1.pc = 0x100;
    f1.chunk.address.region.kind = OSPREY_REGION_GLOBAL;
    f1.chunk.address.region.code_image_id = 0;
    f1.chunk.address.region.site_offset = 0;
    f1.chunk.address.offset = 0;
    f1.chunk.size = 8;
    f1.dynamic_count = 1;
    f1.sample_support = 1;
    f1.is_store = 0;
    f2 = f1;
    f2.pc = 0x200;
    f2.chunk.address.offset = 8;
    CHECK(osprey_table_insert_access(run, &f1) == 1, "insert f1");
    CHECK(osprey_table_insert_access(run, &f2) == 1, "insert f2");
}

/* ------------------------------------------------------------------ */
/* Merge validation                                                    */
/* ------------------------------------------------------------------ */

static void test_overflow_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->overflow = 1;

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "overflow merge status");
    CHECK(osprey_tx_status(ctx) == OSPREY_INCOMPLETE_FACTS,
          "overflow tx status");
    CHECK(strcmp(osprey_tx_stage(ctx), "merge") == 0, "overflow tx stage");
    CHECK(osprey_model(ctx) == NULL, "overflow no model");
    CHECK(ctx->access_facts->len == 0, "overflow no partial merge");
    CHECK(ctx->total_samples == 0, "overflow no sample count");
    CHECK(g_reject_rows == 1, "overflow exactly one reject row");
    CHECK(osprey_analyze(ctx) == OSPREY_INCOMPLETE_FACTS,
          "analyze preserves rejected merge");
    CHECK(g_reject_rows == 1, "analyze does not duplicate rejection");

    osprey_free(ctx);
    g_free(run);
}

static void test_bad_arithmetic_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->bad_arithmetic = 1;

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "bad-arith merge status");
    CHECK(osprey_tx_status(ctx) == OSPREY_INCOMPLETE_FACTS,
          "bad-arith tx status");
    CHECK(strcmp(osprey_tx_stage(ctx), "merge") == 0, "bad-arith tx stage");
    CHECK(ctx->access_facts->len == 0, "bad-arith no partial merge");
    CHECK(g_reject_rows == 1, "bad-arith exactly one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_version_mismatch_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->version = 999;

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "version merge status");
    CHECK(strcmp(osprey_tx_stage(ctx), "merge") == 0, "version tx stage");
    CHECK(ctx->access_facts->len == 0, "version no partial merge");
    CHECK(g_reject_rows == 1, "version exactly one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_capacity_mismatch_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->access_cap = 0;

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "capacity merge status");
    CHECK(strcmp(osprey_tx_stage(ctx), "merge") == 0, "capacity tx stage");
    CHECK(ctx->access_facts->len == 0, "capacity no partial merge");
    CHECK(g_reject_rows == 1, "capacity exactly one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_population_mismatch_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->access_used = 1; /* header claims a record; storage is empty */

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "population merge status");
    CHECK(ctx->access_facts->len == 0, "population no partial merge");
    CHECK(ctx->total_samples == 0, "population no sample count");
    CHECK(g_reject_rows == 1, "population exactly one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_unsupported_execution_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->unsupported_execution = 1;

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_UNSUPPORTED_EXECUTION, "unsupported merge status");
    CHECK(osprey_tx_status(ctx) == OSPREY_UNSUPPORTED_EXECUTION,
          "unsupported tx status");
    CHECK(ctx->access_facts->len == 0, "unsupported no partial merge");
    CHECK(g_reject_rows == 1, "unsupported exactly one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_used_exceeds_cap_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->access_used = run->access_cap + 1;

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "used>cap merge status");
    CHECK(strcmp(osprey_tx_stage(ctx), "merge") == 0, "used>cap tx stage");
    CHECK(ctx->access_facts->len == 0, "used>cap no partial merge");
    CHECK(g_reject_rows == 1, "used>cap exactly one reject row");

    osprey_free(ctx);
    g_free(run);
}

/* ------------------------------------------------------------------ */
/* Happy path + staged install + fail-closed consumer                  */
/* ------------------------------------------------------------------ */

static void test_happy_merge_analyze_and_hide(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    fill_two_access_facts(run);

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "happy merge");
    CHECK(ctx->access_facts->len == 2, "two facts merged");
    CHECK(ctx->total_samples == 1, "one sample committed");
    CHECK(osprey_tx_ok(ctx), "tx ok after merge");
    CHECK(osprey_model(ctx) == NULL, "old model hidden before install");
    CHECK(g_reject_rows == 0, "no reject row on happy merge");

    OspreyStatus st = osprey_analyze(ctx);
    CHECK(st == OSPREY_OK, "analyze ok");
    CHECK(osprey_tx_ok(ctx), "tx ok after analyze");
    CHECK(osprey_model(ctx) != NULL, "model installed on success");
    CHECK(ctx->graph != NULL, "graph committed on success");

    OspreySharedRun *run_pending = new_run(&c);
    fill_two_access_facts(run_pending);
    CHECK(osprey_parent_merge_sample(ctx, run_pending) == OSPREY_OK,
          "new merge starts transaction");
    CHECK(osprey_model(ctx) == NULL,
          "previous model hidden while new transaction is uncommitted");

    /* A later rejected transaction must hide the committed model from
     * consumers while retaining it internally. */
    OspreySharedRun *run2 = new_run(&c);
    run2->overflow = 1;
    CHECK(osprey_parent_merge_sample(ctx, run2) == OSPREY_INCOMPLETE_FACTS,
          "second merge rejects");
    CHECK(osprey_model(ctx) == NULL, "model hidden after rejection");
    CHECK(ctx->model != NULL, "committed model retained internally");
    CHECK(g_reject_rows == 1, "second transaction one reject row");

    osprey_free(ctx);
    g_free(run);
    g_free(run_pending);
    g_free(run2);
}

static void test_recovery_after_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *bad = new_run(&c);
    bad->bad_arithmetic = 1;
    CHECK(osprey_parent_merge_sample(ctx, bad) == OSPREY_INCOMPLETE_FACTS,
          "first merge rejects");
    CHECK(!osprey_tx_ok(ctx), "tx non-ok after rejection");

    /* A fresh baseline transaction recovers. */
    OspreySharedRun *good = new_run(&c);
    fill_two_access_facts(good);
    CHECK(osprey_parent_merge_sample(ctx, good) == OSPREY_OK,
          "recovery merge ok");
    CHECK(osprey_tx_ok(ctx), "tx ok after recovery merge");
    CHECK(osprey_analyze(ctx) == OSPREY_OK, "recovery analyze ok");
    CHECK(osprey_model(ctx) != NULL, "model installed after recovery");
    CHECK(g_reject_rows == 1, "only the first rejection logged");

    osprey_free(ctx);
    g_free(bad);
    g_free(good);
}

/* ------------------------------------------------------------------ */
/* Analysis-stage rejections                                           */
/* ------------------------------------------------------------------ */

static void test_variable_cap_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    c.max_variables = 1;
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    fill_two_access_facts(run);
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");

    OspreyStatus st = osprey_analyze(ctx);
    CHECK(st == OSPREY_LIMIT_EXCEEDED, "variable cap status");
    CHECK(osprey_tx_status(ctx) == OSPREY_LIMIT_EXCEEDED,
          "variable cap tx status");
    CHECK(strcmp(osprey_tx_stage(ctx), "closure") == 0,
          "variable cap tx stage");
    CHECK(osprey_model(ctx) == NULL, "variable cap no model");
    CHECK(g_reject_rows == 1, "variable cap one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_factor_cap_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    c.max_factors = 1;
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    fill_two_access_facts(run);
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");

    OspreyStatus st = osprey_analyze(ctx);
    CHECK(st == OSPREY_LIMIT_EXCEEDED, "factor cap status");
    CHECK(osprey_tx_status(ctx) == OSPREY_LIMIT_EXCEEDED,
          "factor cap tx status");
    CHECK(strcmp(osprey_tx_stage(ctx), "closure") == 0,
          "factor cap tx stage");
    CHECK(osprey_model(ctx) == NULL, "factor cap no model");
    CHECK(g_reject_rows == 1, "factor cap one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_empty_graph_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c); /* no facts at all */
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "empty merge ok");

    OspreyStatus st = osprey_analyze(ctx);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "empty graph status");
    CHECK(osprey_tx_status(ctx) == OSPREY_INCOMPLETE_FACTS,
          "empty graph tx status");
    CHECK(strcmp(osprey_tx_stage(ctx), "infer") == 0,
          "empty graph tx stage");
    CHECK(osprey_model(ctx) == NULL, "empty graph no model");
    CHECK(g_reject_rows == 1, "empty graph one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_exact_component_cap_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    c.max_exact_clique_vars = 1;
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    fill_two_access_facts(run);
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");

    OspreyStatus st = osprey_analyze(ctx);
    CHECK(st == OSPREY_EXACT_COMPONENT_TOO_LARGE, "exact cap status");
    CHECK(strcmp(osprey_tx_stage(ctx), "infer") == 0,
          "exact cap tx stage");
    CHECK(osprey_model(ctx) == NULL, "exact cap no model");
    CHECK(g_reject_rows == 1, "exact cap one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_decoder_cap_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    ctx->graph = osprey_graph_new();
    for (uint32_t i = 0; i < 513; i++) {
        OspreyVar v;
        memset(&v, 0, sizeof(v));
        v.id = i;
        v.kind = OSPREY_PRED_ARRAY;
        v.belief = 1.0;
        v.payload.segment.a1.region.kind = OSPREY_REGION_GLOBAL;
        v.payload.segment.a1.offset = (int64_t)i * 16;
        v.payload.segment.a2 = v.payload.segment.a1;
        v.payload.segment.a2.offset += 8;
        v.payload.segment.size = 8;
        g_array_append_val(ctx->graph->vars, v);
    }
    osprey_tx_begin(ctx);
    OspreyStatus st = osprey_decode(ctx);
    CHECK(st == OSPREY_LIMIT_EXCEEDED, "decoder cap status");
    CHECK(ctx->staged_model == NULL, "decoder cap frees staged model");
    osprey_tx_reject(ctx, st, "decode", "decoder limit exceeded");
    CHECK(osprey_model(ctx) == NULL, "decoder cap no model");
    CHECK(g_reject_rows == 1, "decoder cap one reject row");

    osprey_free(ctx);
}

/* ------------------------------------------------------------------ */

int main(void)
{
    test_overflow_rejection();
    test_bad_arithmetic_rejection();
    test_version_mismatch_rejection();
    test_capacity_mismatch_rejection();
    test_used_exceeds_cap_rejection();
    test_population_mismatch_rejection();
    test_unsupported_execution_rejection();
    test_happy_merge_analyze_and_hide();
    test_recovery_after_rejection();
    test_variable_cap_rejection();
    test_factor_cap_rejection();
    test_empty_graph_rejection();
    test_exact_component_cap_rejection();
    test_decoder_cap_rejection();

    if (failures != 0) {
        fprintf(stderr, "%d unit test check(s) FAILED\n", failures);
        return 1;
    }
    printf("PASS osprey_unit (14/14)\n");
    return 0;
}
