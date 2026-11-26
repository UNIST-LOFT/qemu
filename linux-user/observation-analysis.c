/* Dedicated, bounded, concrete observation analysis.  No solver or replay ABI. */
#include "qemu/osdep.h"
#include "cpu.h"
#include "qemu.h"
#include "tcg-op.h"
#include "exec/helper-proto.h"
#include "observation-analysis.h"
#include "provenance.h"
#include "sem-events.h"
#include "tcg/symbolic/symbolic-instrumentation.h"
#include "syscall_nr.h"

/* Exported by the existing symbolic TCG helper registry. */
const char *tcg_find_helper(TCGContext *s, uintptr_t value);

#define OBS_OBJECTS 2048
#define OBS_BYTES (8u * 1024u * 1024u)
#define OBS_DESCRIPTORS 1000000u
#define OBS_ALLOC_COUNT (16 + TCG_MAX_TEMPS)
#define OBS_ALLOC_SIZE (OBS_ALLOC_COUNT + 1)
#define OBS_DIV_LOW (OBS_ALLOC_SIZE + 1)
#define OBS_DIV_HIGH (OBS_DIV_LOW + 1)
#define OBS_DEPS (OBS_DIV_HIGH + 1)
#define OBS_SOURCES 16

bool observation_analysis_enabled;
static FILE *trace;
static target_ulong patch_pc, image_bias, code_start, code_end, data_start, data_end;
static unsigned event_count, max_events = 2000000, object_count;
static size_t shadow_bytes;
static uint64_t hit_id;
static off_t snapshot_end;
static size_t snapshot_bytes;
static bool hit, ended;
static const char *failure;
static bool defined[OBS_DEPS];
static target_ulong current_pc;
static int allocator_kind;
static target_ulong allocator_old;

typedef struct ObsObject {
    target_ulong base, size, pc;
    uint64_t id;
    uint32_t gen;
    bool live;
    uint8_t *init;
} ObsObject;
static ObsObject *objects;

typedef enum ObsOpKind { O_INSN, O_DEF, O_LOAD, O_STORE, O_BRANCH, O_DIV, O_BAD } ObsOpKind;
typedef struct ObsOp {
    target_ulong pc;
    unsigned kind, dst, count, src[OBS_SOURCES], width, cond;
    bool sign, word32;
} ObsOp;
static ObsOp *descriptors;
static unsigned descriptor_count;
static const ObsOp *pending_access;
static target_ulong pending_addr;
static bool pending_valid;
static const ObsOp *last_access;
static target_ulong last_addr;
static bool have_finding;
static ProvFindingRecord admitted_finding;
static off_t finding_end;
static unsigned finding_sources[OBS_SOURCES], finding_source_count;
static bool modeled_body, external_pending;

static target_ulong normalized(target_ulong pc)
{
    return pc >= code_start && pc < code_end ? pc - image_bias : pc;
}

void observation_analysis_unsupported(const char *reason)
{
    if (observation_analysis_enabled && !have_finding && !failure) failure = reason;
}

static bool event(void)
{
    if (!hit || ended || have_finding || failure) return false;
    if (++event_count > max_events) {
        observation_analysis_unsupported("window_overflow");
        return false;
    }
    return true;
}

static void ids(const unsigned *src, unsigned count)
{
    fputc('[', trace);
    for (unsigned i = 0; i < count; i++) fprintf(trace, "%s%u", i ? "," : "", src[i]);
    fputc(']', trace);
}

static void need(const ObsOp *op)
{
    for (unsigned i = 0; i < op->count; i++) {
        if (op->src[i] >= OBS_DEPS || !defined[op->src[i]]) {
            observation_analysis_unsupported("undefined-scratch-live-in");
        }
    }
}

static ObsObject *object_at(target_ulong addr)
{
    static ObsObject *cache[2];
    static unsigned next;
    for (unsigned i = 0; i < G_N_ELEMENTS(cache); i++) {
        ObsObject *o = cache[i];
        if (o && o->live && addr >= o->base && addr - o->base < o->size) return o;
    }
    for (unsigned i = object_count; i > 0; i--) {
        ObsObject *o = &objects[i - 1];
        if (o->live && addr >= o->base && addr - o->base < o->size) {
            cache[next++ & 1] = o;
            return o;
        }
    }
    return NULL;
}

static bool initialized(target_ulong addr)
{
    ObsObject *o = object_at(addr);
    if (!o) return true;
    size_t bit = addr - o->base;
    return (o->init[bit >> 3] >> (bit & 7)) & 1;
}

static void set_initialized(target_ulong addr, bool value)
{
    ObsObject *o = object_at(addr);
    if (!o) return;
    size_t bit = addr - o->base;
    if (value) o->init[bit >> 3] |= 1u << (bit & 7);
    else o->init[bit >> 3] &= ~(1u << (bit & 7));
}

void observation_analysis_store(target_ulong addr, target_ulong size)
{
    if (!observation_analysis_enabled) return;
    if (size > OBS_BYTES || addr + size < addr) {
        observation_analysis_unsupported("write-interval-capacity");
        return;
    }
    ObsObject *single = object_at(addr);
    if (single && size <= single->size - (addr - single->base)) {
        for (target_ulong i = 0; i < size; i++) {
            size_t bit = addr - single->base + i;
            single->init[bit >> 3] |= 1u << (bit & 7);
        }
        return;
    }
    for (unsigned i = 0; i < object_count; i++) {
        ObsObject *o = &objects[i];
        if (!o->live) continue;
        target_ulong lo = MAX(addr, o->base), hi = MIN(addr + size, o->base + o->size);
        for (target_ulong a = lo; a < hi; a++) {
            size_t bit = a - o->base;
            o->init[bit >> 3] |= 1u << (bit & 7);
        }
    }
}

/* lock_user validates QEMU guest permissions.  Never call guest syscalls to
 * read snapshots, and never dereference unchecked guest pointers. */
static bool region(const char *kind, target_ulong base, target_ulong size,
                   const ObsObject *object, bool *comma)
{
    if (size > OBS_BYTES || base + size < base) return false;
    void *p = size ? lock_user(VERIFY_READ, base, size, 1) : NULL;
    if (size && !p) return false;
    fprintf(trace, "%s{\"kind\":\"%s\",\"base\":%" PRIu64 ",\"size\":%" PRIu64,
            *comma ? "," : "", kind, (uint64_t)base, (uint64_t)(object ? object->size : size));
    *comma = true;
    if (object) fprintf(trace, ",\"object_id\":%" PRIu64 ",\"generation\":%u,\"alloc_pc\":%" PRIu64 ",\"state\":\"%s\"",
                        object->id, object->gen, (uint64_t)normalized(object->pc), object->live ? "live" : "freed");
    fprintf(trace, ",\"data\":\"");
    for (target_ulong i = 0; i < size; i++) fprintf(trace, "%02x", ((uint8_t *)p)[i]);
    fprintf(trace, "\",\"init\":\"");
    for (target_ulong i = 0; i < size; i += 8) {
        unsigned bits = 0;
        for (unsigned j = 0; j < 8 && i + j < size; j++) {
            bool valid = object ? ((object->init[(i + j) >> 3] >> ((i + j) & 7)) & 1) : true;
            if (valid) bits |= 1u << j;
        }
        fprintf(trace, "%02x", bits);
    }
    fprintf(trace, "\"}");
    if (p) unlock_user(p, base, 0);
    return true;
}

static void snapshot(CPUArchState *env)
{
    if (failure || have_finding) return;
    size_t projected = data_end - data_start;
    if (projected > OBS_BYTES - 4096) {
        observation_analysis_unsupported("cumulative-snapshot-capacity");
        return;
    }
    projected += 4096;
    for (unsigned i = 0; i < object_count; i++) {
        if (!objects[i].live) continue;
        if (objects[i].size > OBS_BYTES - projected) {
            observation_analysis_unsupported("cumulative-snapshot-capacity");
            return;
        }
        projected += objects[i].size;
    }
    if (projected > OBS_BYTES - MIN(snapshot_bytes, OBS_BYTES)) {
        observation_analysis_unsupported("cumulative-snapshot-capacity");
        return;
    }
    bool first_hit = !hit;
    if (hit && ++hit_id >= 1024) {
        observation_analysis_unsupported("patch-visit-capacity");
        return;
    }
    hit = true;
    event_count = 0;
    pending_valid = false;
    have_finding = false;
    external_pending = false;
    /* Keep every bounded snapshot for any-visit initialization filtering,
     * but replace the old event window. snapshot_end precedes those events. */
    if (fflush(trace) || ftruncate(fileno(trace), snapshot_end) ||
        fseeko(trace, snapshot_end, SEEK_SET)) {
        observation_analysis_unsupported("trace-write-failed");
        return;
    }
    if (first_hit) fprintf(trace, "{\"kind\":\"header\",\"schema_version\":1}\n");
    fprintf(trace, "{\"kind\":\"patch\",\"hit_id\":%" PRIu64 ",\"pc\":%" PRIu64 ",\"load_bias\":%" PRIu64 ",\"regs\":[", hit_id, (uint64_t)patch_pc, (uint64_t)image_bias);
    for (unsigned i = 0; i < 16; i++) fprintf(trace, "%s%" PRIu64, i ? "," : "", (uint64_t)env->regs[i]);
    fprintf(trace, "],\"regions\":[");
    bool comma = false;
    size_t total = data_end - data_start;
    if (total > OBS_BYTES || (total && !region("global", data_start, total, NULL, &comma))) {
        observation_analysis_unsupported("global-snapshot-unreadable-or-capacity");
    }
    target_ulong sp = env->regs[R_ESP];
    target_ulong stack_size = 0;
    while (stack_size < 4096 && access_ok(VERIFY_READ, sp + stack_size, 1)) stack_size++;
    if (stack_size && !region("stack", sp, stack_size, NULL, &comma)) observation_analysis_unsupported("stack-snapshot-unreadable");
    total += stack_size;
    for (unsigned i = 0; i < object_count; i++) {
        ObsObject *o = &objects[i];
        target_ulong n = o->live ? o->size : 0;
        if (n > OBS_BYTES - MIN(total, OBS_BYTES) || !region("heap", o->base, n, o, &comma)) {
            observation_analysis_unsupported("heap-snapshot-unreadable-or-capacity");
            break;
        }
        total += n;
    }
    fprintf(trace, "]}\n");
    if (total > OBS_BYTES - MIN(snapshot_bytes, OBS_BYTES)) {
        observation_analysis_unsupported("cumulative-snapshot-capacity");
    } else snapshot_bytes += total;
    snapshot_end = ftello(trace);
    if (snapshot_end < 0) observation_analysis_unsupported("trace-position-failed");
    memset(defined, 0, sizeof(defined));
    for (unsigned i = 0; i < 16; i++) defined[i] = true;
}

static bool compare(unsigned cond, uint64_t a, uint64_t b, bool word32)
{
    if (word32) { a = (uint32_t)a; b = (uint32_t)b; }
    int64_t sa = word32 ? (int32_t)a : (int64_t)a;
    int64_t sb = word32 ? (int32_t)b : (int64_t)b;
    switch (cond) {
    case TCG_COND_EQ: return a == b;
    case TCG_COND_NE: return a != b;
    case TCG_COND_LT: return sa < sb;
    case TCG_COND_GE: return sa >= sb;
    case TCG_COND_LE: return sa <= sb;
    case TCG_COND_GT: return sa > sb;
    case TCG_COND_LTU: return a < b;
    case TCG_COND_GEU: return a >= b;
    case TCG_COND_LEU: return a <= b;
    case TCG_COND_GTU: return a > b;
    default: observation_analysis_unsupported("unsupported-branch-condition"); return false;
    }
}

static void record(uint64_t descriptor, uint64_t a, uint64_t b)
{
    if (have_finding || ended) return;
    const ObsOp *op = (const ObsOp *)(uintptr_t)descriptor;
    CPUArchState *env = thread_cpu->env_ptr;
    if (op->kind == O_INSN) {
        if (op->pc < code_start || op->pc >= code_end) {
            if (hit && !modeled_body && !sem_allocator_body) external_pending = true;
            return;
        }
        if (external_pending && op->pc != patch_pc + image_bias) observation_analysis_unsupported("unsupported-external-call-effects");
        external_pending = false;
        current_pc = op->pc;
        pending_valid = false;
        if (op->dst) memset(defined + op->dst, 0, (OBS_ALLOC_COUNT - op->dst) * sizeof(bool));
        if (op->pc == patch_pc + image_bias) snapshot(env);
        return;
    }
    if (sem_allocator_body) return;
    if (op->kind == O_LOAD || op->kind == O_STORE || op->kind == O_DIV) {
        pending_access = op;
        pending_addr = a;
        pending_valid = true;
        return;
    }
    if (!event()) return;
    if (op->kind == O_BAD) { observation_analysis_unsupported("unsupported-tcg-semantics"); return; }
    need(op);
    if (op->kind == O_BRANCH) {
        fprintf(trace, "{\"kind\":\"branch\",\"pc\":%" PRIu64 ",\"src\":", (uint64_t)normalized(op->pc));
        ids(op->src, op->count);
        fprintf(trace, ",\"taken\":%s}\n", compare(op->cond, a, b, op->word32) ? "true" : "false");
    } else {
        defined[op->dst] = true;
        fprintf(trace, "{\"kind\":\"def\",\"pc\":%" PRIu64 ",\"dst\":%u,\"src\":", (uint64_t)normalized(op->pc), op->dst);
        ids(op->src, op->count);
        fprintf(trace, "}\n");
    }
}

static void commit(uint64_t unused, uint64_t a, uint64_t b)
{
    if (have_finding || ended) return;
    (void)unused; (void)a; (void)b;
    if (!pending_valid || sem_allocator_body) return;
    const ObsOp *op = pending_access;
    target_ulong addr = pending_addr;
    last_access = op; last_addr = addr;
    pending_valid = false;
    if (op->kind == O_STORE) observation_analysis_store(addr, op->width);
    if (op->pc < code_start || op->pc >= code_end) return;
    if (!event()) return;
    need(op);
    fprintf(trace, "{\"kind\":\"%s\",\"pc\":%" PRIu64 ",\"addr\":%" PRIu64 ",\"size\":%u,", op->kind == O_LOAD ? "load" : "store", (uint64_t)normalized(op->pc), (uint64_t)addr, op->width);
    if (op->kind == O_LOAD) {
        fprintf(trace, "\"dst\":%u,\"signed\":%s,\"addr_regs\":", op->dst, op->sign ? "true" : "false");
        ids(op->src, op->count);
        defined[op->dst] = true;
    } else {
        fprintf(trace, "\"src\":[%u],\"addr_regs\":", op->dst);
        if (!defined[op->dst]) observation_analysis_unsupported("undefined-scratch-live-in");
        ids(op->src, op->count);
    }
    fprintf(trace, "}\n");
}

/* Insert before optimization/liveness.  Unlike symbolic post-liveness
 * instrumentation these calls participate in ordinary TCG allocation. */
static void call(TCGContext *s, TCGOp *anchor, bool after, void *fn,
                 const ObsOp *desc, TCGArg a, TCGArg b, bool word32)
{
    TCGOp *at = anchor;
    TCGTemp *args[3];
    for (unsigned i = 0; i < 3; i++) args[i] = tcg_temp_new_internal(TCG_TYPE_I64, false);
    for (unsigned i = 0; i < 3; i++) {
        bool supplied = i == 1 ? a != (TCGArg)-1 : i == 2 && b != (TCGArg)-1;
        TCGOpcode opc = supplied ? (word32 ? INDEX_op_extu_i32_i64 : INDEX_op_mov_i64) : INDEX_op_movi_i64;
        TCGOp *p = after ? tcg_op_insert_after(s, at, opc) : tcg_op_insert_before(s, anchor, opc);
        p->args[0] = temp_arg(args[i]);
        p->args[1] = supplied ? (i == 1 ? a : b) : (i == 0 ? (uintptr_t)desc : 0);
        at = p;
    }
    TCGOp *p = after ? tcg_op_insert_after(s, at, INDEX_op_call) : tcg_op_insert_before(s, anchor, INDEX_op_call);
    for (unsigned i = 0; i < 3; i++) p->args[i] = temp_arg(args[i]);
    p->args[3] = (uintptr_t)fn; p->args[4] = 0;
    TCGOP_CALLI(p) = 3; TCGOP_CALLO(p) = 0;
    for (unsigned i = 0; i < 3; i++) tcg_temp_free_internal(args[i]);
}

static unsigned dependency(TCGContext *s, TCGArg arg)
{
    TCGTemp *t = arg_temp(arg);
    unsigned index = t - s->temps;
    static const char *const names[16] = {"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"};
    if (index < s->nb_globals && t->name) {
        for (unsigned i = 0; i < 16; i++) if (!strcmp(t->name, names[i])) return i;
    }
    return 16 + index;
}

static ObsOp *descriptor(void)
{
    if (descriptor_count == OBS_DESCRIPTORS) {
        observation_analysis_unsupported("translation-capacity");
        return NULL;
    }
    return &descriptors[descriptor_count++];
}

void observation_analysis_instrument(TCGContext *s)
{
    if (!observation_analysis_enabled) return;
    if (s->nb_temps > TCG_MAX_TEMPS - 3) {
        observation_analysis_unsupported("translation-temp-capacity");
        return;
    }
    TCGTempSet saved[TCG_TYPE_COUNT * 2];
    memcpy(saved, s->free_temps, sizeof(saved));
    /* Never reuse a translator temp still present in the raw op stream. */
    memset(s->free_temps, 0, sizeof(s->free_temps));
    TCGOp *op, *next;
    target_ulong pc = 0;
    bool first = true;
    QTAILQ_FOREACH_SAFE(op, &s->ops, link, next) {
        if (op->opc == INDEX_op_insn_start) pc = op->args[0];
        bool main = pc >= code_start && pc < code_end;
        bool mem = op->opc == INDEX_op_qemu_ld_i64 || op->opc == INDEX_op_qemu_ld_i32 || op->opc == INDEX_op_qemu_st_i64 || op->opc == INDEX_op_qemu_st_i32;
        if (!main && !mem && op->opc != INDEX_op_insn_start) continue;
        const TCGOpDef *def = &tcg_op_defs[op->opc];
        unsigned no = def->nb_oargs, ni = def->nb_iargs;
        bool branch = op->opc == INDEX_op_brcond_i64 || op->opc == INDEX_op_brcond_i32;
        if (op->opc == INDEX_op_call) {
            no = TCGOP_CALLO(op); ni = TCGOP_CALLI(op);
            const char *name = tcg_find_helper(s, op->args[no + ni]);
            if (name && (!strncmp(name, "sem_", 4) || !strncmp(name, "lookup_tb", 9) || !strcmp(name, "raise_exception") || !strcmp(name, "syscall") || !strcmp(name, "exit_atomic"))) continue;
            /* Only helpers with explicit outputs and no hidden guest state
             * are expressible as a def. Flag evaluation is pure. */
            if (!name || (strncmp(name, "cc_compute_", 11) && strncmp(name, "div", 3) && strncmp(name, "idiv", 4))) {
                ObsOp *bad = descriptor(); if (!bad) break;
                *bad = (ObsOp){.pc = pc, .kind = O_BAD};
                call(s, op, false, record, bad, -1, -1, false);
                continue;
            }
            if (!no && (!strcmp(name, "divl_EAX") || !strcmp(name, "idivl_EAX") ||
                        !strcmp(name, "divq_EAX") || !strcmp(name, "idivq_EAX"))) {
                ObsOp *d = descriptor(); if (!d) break;
                *d = (ObsOp){.pc = pc, .kind = O_DIV};
                for (unsigned i = 0; i < ni; i++) {
                    TCGArg arg = op->args[i];
                    if (arg != TCG_CALL_DUMMY_ARG && !arg_temp(arg)->fixed_reg && d->count < OBS_SOURCES) d->src[d->count++] = dependency(s, arg);
                }
                for (unsigned i = 0; i < 2; i++) {
                    ObsOp *saved_value = descriptor(); if (!saved_value) break;
                    *saved_value = (ObsOp){.pc = pc, .kind = O_DEF, .dst = OBS_DIV_LOW + i, .count = 1};
                    saved_value->src[0] = i ? 2 : 0;
                    call(s, op, false, record, saved_value, -1, -1, false);
                }
                call(s, op, false, record, d, -1, -1, false);
                for (unsigned i = 0; i < 2; i++) {
                    ObsOp *result = descriptor(); if (!result) break;
                    *result = *d; result->kind = O_DEF; result->dst = i ? 2 : 0;
                    result->src[result->count++] = OBS_DIV_LOW;
                    result->src[result->count++] = OBS_DIV_HIGH;
                    call(s, op, true, record, result, -1, -1, false);
                }
                continue;
            }
            if (!no) {
                ObsOp *bad = descriptor(); if (!bad) break;
                *bad = (ObsOp){.pc = pc, .kind = O_BAD};
                call(s, op, false, record, bad, -1, -1, false);
                continue;
            }
        }
        if (op->opc == INDEX_op_insn_start) {
            ObsOp *d = descriptor(); if (!d) break;
            *d = (ObsOp){.pc = pc, .kind = O_INSN, .dst = first ? 16u + s->nb_globals : 0};
            first = false;
            call(s, op, true, record, d, -1, -1, false);
        } else if (mem) {
            ObsOp *d = descriptor(); if (!d) break;
            TCGMemOp mo = get_memop(op->args[2]);
            bool load = op->opc == INDEX_op_qemu_ld_i64 || op->opc == INDEX_op_qemu_ld_i32;
            *d = (ObsOp){.pc = pc, .kind = load ? O_LOAD : O_STORE, .dst = dependency(s, op->args[0]), .count = 1, .width = 1u << (mo & MO_SIZE), .sign = (mo & MO_SIGN) != 0};
            d->src[0] = dependency(s, op->args[1]);
            call(s, op, false, record, d, op->args[1], -1, false);
            call(s, op, true, commit, d, -1, -1, false);
        } else if (no > 1 || (no && !strncmp(def->name, "ld", 2))) {
            ObsOp *d = descriptor(); if (!d) break;
            *d = (ObsOp){.pc = pc, .kind = O_BAD};
            call(s, op, false, record, d, -1, -1, false);
        } else if (branch || no) {
            if (ni > OBS_SOURCES) { observation_analysis_unsupported("dependency-capacity"); break; }
            for (unsigned out = 0; out < (branch ? 1 : no); out++) {
                ObsOp *d = descriptor(); if (!d) break;
                *d = (ObsOp){.pc = pc, .kind = branch ? O_BRANCH : O_DEF, .dst = branch ? 0 : dependency(s, op->args[out]), .word32 = op->opc == INDEX_op_brcond_i32};
                for (unsigned i = 0; i < ni; i++) {
                    TCGArg arg = op->args[no + i];
                    if (arg == TCG_CALL_DUMMY_ARG || arg_temp(arg)->fixed_reg) continue;
                    d->src[d->count++] = dependency(s, arg);
                }
                if (branch) d->cond = op->args[2];
                call(s, op, false, record, d, branch ? op->args[0] : (TCGArg)-1, branch ? op->args[1] : (TCGArg)-1, d->word32);
            }
        } else if (main && (op->opc == INDEX_op_st_i64 || op->opc == INDEX_op_st_i32 || op->opc == INDEX_op_st8_i32 || op->opc == INDEX_op_st16_i32 || op->opc == INDEX_op_st8_i64 || op->opc == INDEX_op_st16_i64 || op->opc == INDEX_op_st32_i64)) {
            /* Instruction-pointer publication is control state, not a scalar
             * observation. Other hidden CPU writes fail closed. */
            if (arg_temp(op->args[1])->fixed_reg && op->args[2] == offsetof(CPUX86State, eip)) continue;
            ObsOp *d = descriptor(); if (!d) break;
            *d = (ObsOp){.pc = pc, .kind = O_BAD};
            call(s, op, false, record, d, -1, -1, false);
        }
    }
    memcpy(s->free_temps, saved, sizeof(saved));
}

void observation_analysis_image(target_ulong bias, target_ulong code,
                                target_ulong end, target_ulong data,
                                target_ulong dend)
{
    if (!observation_analysis_enabled) return;
    image_bias = bias; code_start = code; code_end = end;
    data_start = data; data_end = dend;
    if (patch_pc + bias < code || patch_pc + bias >= end) observation_analysis_unsupported("patch-outside-main-image");
}

void observation_analysis_allocator(CPUArchState *env, int kind, target_ulong old_base)
{
    (void)env;
    if (!observation_analysis_enabled) return;
    allocator_kind = kind; allocator_old = old_base;
    if (hit && !failure) {
        unsigned args[2] = {7, 6};
        for (unsigned i = 0; i < 2; i++) {
            if (!event()) break;
            fprintf(trace, "{\"kind\":\"def\",\"pc\":%" PRIu64 ",\"dst\":%u,\"src\":[%u]}\n", (uint64_t)normalized(current_pc), OBS_ALLOC_COUNT + i, args[i]);
            defined[OBS_ALLOC_COUNT + i] = defined[args[i]];
        }
    }
}

void observation_analysis_clobber(void)
{
    if (!observation_analysis_enabled) return;
    const unsigned saved[] = {0, 1, 2, 6, 7, 8, 9, 10, 11};
    for (unsigned i = 0; i < G_N_ELEMENTS(saved); i++) defined[saved[i]] = false;
}

void observation_analysis_return_pointer(void)
{
    if (!observation_analysis_enabled || !event()) return;
    fprintf(trace, "{\"kind\":\"def\",\"pc\":%" PRIu64 ",\"dst\":0,\"src\":[%u]}\n", (uint64_t)normalized(current_pc), OBS_ALLOC_COUNT);
    defined[0] = defined[OBS_ALLOC_COUNT];
}

void observation_analysis_model(bool active, bool supported)
{
    if (!observation_analysis_enabled) return;
    modeled_body = active;
    if (hit && !supported) observation_analysis_unsupported("unsupported-libc-model-dependencies");
}

void observation_analysis_alloc(target_ulong base, target_ulong size, target_ulong pc,
                                uint64_t id, uint32_t gen, int producer)
{
    if (!observation_analysis_enabled) return;
    if (object_count == OBS_OBJECTS || size > OBS_BYTES || shadow_bytes + size > OBS_BYTES || base + size < base) {
        observation_analysis_unsupported("object-or-shadow-capacity"); return;
    }
    ObsObject *o = &objects[object_count++];
    *o = (ObsObject){.base = base, .size = size, .pc = pc, .id = id, .gen = gen, .live = true};
    o->init = g_malloc0((size + 7) / 8 + 1);
    shadow_bytes += size;
    if (producer == PROV_PRODUCER_CALLOC_RETURN) memset(o->init, 255, (size + 7) / 8);
    if (producer == PROV_PRODUCER_REALLOC_RETURN) {
        for (unsigned i = object_count - 1; i > 0; i--) {
            ObsObject *old = &objects[i - 1];
            if (old->base != allocator_old) continue;
            target_ulong n = MIN(size, old->size);
            for (target_ulong j = 0; j < n; j++) if ((old->init[j >> 3] >> (j & 7)) & 1) o->init[j >> 3] |= 1u << (j & 7);
            break;
        }
    }
    if (!event()) return;
    fprintf(trace, "{\"kind\":\"alloc\",\"pc\":%" PRIu64 ",\"addr\":%" PRIu64 ",\"size\":%" PRIu64 ",\"object_id\":%" PRIu64 ",\"generation\":%u,\"src\":[", (uint64_t)normalized(pc), (uint64_t)base, (uint64_t)size, id, gen);
    if (allocator_kind == PROV_OP_REALLOC) fprintf(trace, "%u", OBS_ALLOC_SIZE);
    else {
        fprintf(trace, "%u", OBS_ALLOC_COUNT);
        if (allocator_kind == PROV_OP_CALLOC) fprintf(trace, ",%u", OBS_ALLOC_SIZE);
    }
    fprintf(trace, "],\"dst\":0}\n");
    defined[0] = true;
}

void observation_analysis_free(target_ulong base)
{
    if (!observation_analysis_enabled) return;
    ObsObject *o = NULL;
    for (unsigned i = object_count; i > 0; i--) if (objects[i - 1].base == base && objects[i - 1].live) { o = &objects[i - 1]; break; }
    if (!o) return;
    o->live = false;
    if (event()) fprintf(trace, "{\"kind\":\"free\",\"pc\":%" PRIu64 ",\"addr\":%" PRIu64 ",\"object_id\":%" PRIu64 ",\"generation\":%u,\"src\":[%u]}\n", (uint64_t)normalized(current_pc), (uint64_t)base, o->id, o->gen, OBS_ALLOC_COUNT);
}

void observation_analysis_copy(CPUArchState *env, target_ulong src, target_ulong dst, target_ulong size)
{
    (void)env;
    if (!observation_analysis_enabled) return;
    if (size > OBS_BYTES || src + size < src || dst + size < dst) { observation_analysis_unsupported("copy-capacity"); return; }
    if (dst > src) for (target_ulong i = size; i > 0; i--) set_initialized(dst + i - 1, initialized(src + i - 1));
    else for (target_ulong i = 0; i < size; i++) set_initialized(dst + i, initialized(src + i));
    if (event()) fprintf(trace, "{\"kind\":\"copy\",\"pc\":%" PRIu64 ",\"src_addr\":%" PRIu64 ",\"dst_addr\":%" PRIu64 ",\"size\":%" PRIu64 "}\n", (uint64_t)normalized(current_pc), (uint64_t)src, (uint64_t)dst, (uint64_t)size);
}

void observation_analysis_overwrite(CPUArchState *env, target_ulong addr, target_ulong size, int cls)
{
    (void)env;
    if (!observation_analysis_enabled || !size) return;
    observation_analysis_store(addr, size);
    if (cls == SEM_OP_SYSCALL && env &&
        (env->regs[R_EAX] == TARGET_NR_read || env->regs[R_EAX] == TARGET_NR_pread64)) {
        observation_analysis_read(env, addr, size);
    } else if (cls == SEM_OP_SYSCALL) {
        /* Actual external reads are emitted by the syscall return hook. Other
         * kernel outputs are not input payload or invented constants. */
        if (hit) observation_analysis_unsupported("unsupported-syscall-overwrite");
    } else if (cls == SEM_OP_LIBC_MODEL) {
        if (hit && !defined[OBS_ALLOC_SIZE]) observation_analysis_unsupported("unsupported-libc-overwrite-dependencies");
        if (event()) fprintf(trace, "{\"kind\":\"overwrite\",\"pc\":%" PRIu64 ",\"addr\":%" PRIu64 ",\"size\":%" PRIu64 ",\"src\":[%u]}\n", (uint64_t)normalized(current_pc), (uint64_t)addr, (uint64_t)size, OBS_ALLOC_SIZE);
    } else if (hit) observation_analysis_unsupported("unsupported-semantic-overwrite");
}

void observation_analysis_syscall_return(void)
{
    if (!observation_analysis_enabled) return;
    /* Return/error codes and syscall-clobbered flags are external results,
     * not invented constants or patch live-ins. Consumers fail closed until
     * a modeled definition replaces them. */
    defined[0] = defined[1] = defined[11] = false;
}

void observation_analysis_read(CPUArchState *env, target_ulong addr, target_ulong size)
{
    (void)env;
    if (!observation_analysis_enabled || !size) return;
    observation_analysis_store(addr, size);
    if (event()) fprintf(trace, "{\"kind\":\"sys_read\",\"pc\":%" PRIu64 ",\"addr\":%" PRIu64 ",\"size\":%" PRIu64 ",\"src\":[]}\n", (uint64_t)normalized(current_pc), (uint64_t)addr, (uint64_t)size);
}

void observation_analysis_signal(CPUArchState *env, int sig, target_ulong addr)
{
    if (!observation_analysis_enabled || ended) return;
    if (!have_finding && event()) {
        fprintf(trace, "{\"kind\":\"fault\",\"pc\":%" PRIu64 ",\"fault_kind\":\"signal-%d\",\"regs\":", (uint64_t)normalized(env->eip), sig);
        if (pending_valid) { need(pending_access); ids(pending_access->src, pending_access->count); }
        else if (sig == TARGET_SIGABRT) fprintf(trace, "[]");
        else { fprintf(trace, "[]"); observation_analysis_unsupported("unsupported-signal-seed"); }
        fprintf(trace, ",\"mem\":[");
        if (pending_valid && pending_access->kind != O_DIV) fprintf(trace, "{\"addr\":%" PRIu64 ",\"size\":%u}", (uint64_t)(addr ? addr : pending_addr), pending_access->width);
        fprintf(trace, "]}\n");
    }
    observation_analysis_finish(env);
}

void observation_analysis_finding(void)
{
    if (!observation_analysis_enabled || ended) return;
    ProvPublishedFinding preferred;
    if (!provenance_snapshot_pending_finding(&preferred)) return;
    const ProvFindingRecord *f = &preferred.payload;
    if (have_finding) {
        /* coverage-v7 admits promotion only for the same origin, actual PC,
         * address and width. Never infer a replacement or move its cursor. */
        if (f->origin != admitted_finding.origin ||
            f->actual_pc != admitted_finding.actual_pc ||
            f->access_addr != admitted_finding.access_addr ||
            f->access_width != admitted_finding.access_width) {
            failure = "inconsistent-provenance-publication";
            return;
        }
        admitted_finding = *f;
        return;
    }
    if (!event()) return;
    finding_source_count = 0;
    if (f->access_width > OBS_BYTES) {
        observation_analysis_unsupported("unsupported-fault-interval-capacity");
    }
    if (f->origin == PROV_FINDING_ORIGIN_SYSCALL_REQUEST) {
        CPUArchState *env = thread_cpu->env_ptr;
        if (env->regs[R_EAX] == TARGET_NR_write &&
            f->actual_pc >= code_start && f->actual_pc < code_end) {
            finding_sources[finding_source_count++] = 6; /* RSI buffer */
            finding_sources[finding_source_count++] = 2; /* RDX request */
        } else {
            /* writev lengths originate in guest iovecs, not a GPR length.
             * Do not pretend the iovec count is the requested payload size. */
            observation_analysis_unsupported("unsupported-syscall-request-fault-seed");
        }
    } else {
        const ObsOp *access = pending_valid && pending_access->pc == f->actual_pc &&
            pending_addr == f->access_addr ? pending_access :
            last_access && last_access->pc == f->actual_pc &&
            last_addr == f->access_addr ? last_access : NULL;
        if (access) {
            finding_source_count = access->count;
            memcpy(finding_sources, access->src,
                   finding_source_count * sizeof(finding_sources[0]));
        } else if (f->ea_base_reg >= 0 && f->ea_base_reg < 16) {
            finding_sources[finding_source_count++] = f->ea_base_reg;
        } else {
            observation_analysis_unsupported("unsupported-provenance-fault-seed");
        }
    }
    ObsOp seed = {.count = finding_source_count};
    memcpy(seed.src, finding_sources, finding_source_count * sizeof(seed.src[0]));
    need(&seed);
    finding_end = ftello(trace);
    if (finding_end < 0) observation_analysis_unsupported("trace-position-failed");
    admitted_finding = *f;
    have_finding = true;
}

static void publish_finding(void)
{
    if (!have_finding) return;
    if (fflush(trace) || finding_end < 0 ||
        ftruncate(fileno(trace), finding_end) ||
        fseeko(trace, finding_end, SEEK_SET)) {
        failure = "trace-write-failed";
        return;
    }
    const ProvFindingRecord *f = &admitted_finding;
    const char *kind = f->origin == PROV_FINDING_ORIGIN_SYSCALL_REQUEST ?
        "syscall-request" : f->is_uaf ? "heap-use-after-free" : "heap-buffer-overflow";
    fprintf(trace, "{\"kind\":\"fault\",\"pc\":%" PRIu64
            ",\"fault_kind\":\"%s\",\"object_id\":%" PRIu64
            ",\"generation\":%u,\"object_base\":%" PRIu64
            ",\"requested_size\":%" PRIu64 ",\"tracked_offset\":%" PRId64
            ",\"actual_pc\":%" PRIu64 ",\"quality\":\"%s\",\"regs\":",
            (uint64_t)normalized(f->access_pc), kind, f->object_id, f->generation,
            (uint64_t)f->object_base, (uint64_t)f->requested_size,
            f->tracked_offset, (uint64_t)f->actual_pc,
            f->quality == PROV_FINDING_TAGGED ? "tagged" : "fallback");
    ids(finding_sources, finding_source_count);
    fprintf(trace, ",\"mem\":[{\"addr\":%" PRIu64 ",\"size\":%" PRIu64 "}]}\n",
            (uint64_t)f->access_addr, (uint64_t)f->access_width);
}

void observation_analysis_finish(CPUArchState *env)
{
    (void)env;
    if (!observation_analysis_enabled || ended) return;
    if (!hit && !failure) failure = "patch-not-reached";
    publish_finding();
    fprintf(trace, "{\"kind\":\"end\",\"status\":\"%s\"}\n", failure ? failure : "ok");
    if (fflush(trace) || ferror(trace)) fprintf(stderr, "observation-analysis: trace-write-failed\n");
    ended = true;
}

void observation_analysis_init(void)
{
    const char *enabled = getenv("BINRADAR_OBS_ANALYSIS");
    if (!enabled || !strcmp(enabled, "0")) return;
    if (strcmp(enabled, "1")) { fprintf(stderr, "observation-analysis: invalid opt-in\n"); exit(1); }
#if !defined(TARGET_X86_64)
    fprintf(stderr, "observation-analysis: x86-64 only\n"); exit(1);
#endif
    const char *incompatible[] = {"BINRADAR_FORKSERVER_ENABLE", "BINRADAR_REPLAY_SERVER", "BINRADAR_OSPREY_ENABLE", "E9_EXCLUDE_RANGES", "E9_RELOCATED_INSTRUCTIONS"};
    for (unsigned i = 0; i < G_N_ELEMENTS(incompatible); i++) {
        const char *v = getenv(incompatible[i]);
        if (v && *v && strcmp(v, "0")) { fprintf(stderr, "observation-analysis: incompatible %s\n", incompatible[i]); exit(1); }
    }
    const char *location = getenv("BINRADAR_OBS_PATCH_LOC"), *path = getenv("BINRADAR_OBS_TRACE_FILE");
    char *end;
    errno = 0;
    patch_pc = location ? strtoull(location, &end, 0) : 0;
    if (!location || errno || !*location || *end || !patch_pc || !path || !*path || !getenv("PLT_INFO_FILE")) {
        fprintf(stderr, "observation-analysis: patch, trace path and PLT_INFO_FILE required\n"); exit(1);
    }
    const char *cap = getenv("BINRADAR_OBS_MAX_EVENTS");
    if (cap) {
        errno = 0; uint64_t n = strtoull(cap, &end, 10);
        if (errno || !*cap || *end || !n || n > 2000000) { fprintf(stderr, "observation-analysis: invalid event cap\n"); exit(1); }
        max_events = n;
    }
    trace = fopen(path, "w+");
    if (!trace) { perror("observation-analysis trace"); exit(1); }
    fprintf(trace, "{\"kind\":\"header\",\"schema_version\":1}\n"); fflush(trace);
    objects = g_new0(ObsObject, OBS_OBJECTS);
    descriptors = g_new0(ObsOp, OBS_DESCRIPTORS);
    observation_analysis_enabled = true;
    binradar_memcheck_enabled = 1;
}
