#!/usr/bin/env python3
"""Provenance (pointer-analysis / memcheck) test harness runner.

Runs each guest under the tracer in the mode the test requires and asserts
on the structured `[prov]` / `[snapshot]` / `[forkserver]` stderr log lines.

Modes
-----
memcheck   : plain tracer (-d page), BINRADAR_MEMCHECK_ENABLE=1, no solver.
             Covers allocation-lifecycle / tag-transfer / region tests.
symbolic   : -symbolic + live solver (SHM pools). Required for libc models
             (memcpy/memset/memchr) and for the deferred-continuation and
             crash-precedence tests.
forkserver : -symbolic + solver + forkserver pipes. The driver performs the
             handshake and runs one child iteration, then closes the ctrl
             pipe (tracer exits 2 on EOF).

Invocation (see Makefile):
    run_test.py GUESTS WORK QEMU SOLVER [--quiet]

Exit status: 0 if every test passes, 1 otherwise.
"""

import argparse
import os
import random
import re
import struct
import subprocess
import sys
import tempfile
import time

# ---------------------------------------------------------------------------
# Test configuration
# ---------------------------------------------------------------------------
# mode: mem | sym | fork
# exit_verdict: 'normal' | 'crash' | 'signal' — the [snapshot] [exit] verdict
#     'signal' = guest died from an unhandled host/target signal; the exit
#     record is still [crash] but the reason is unhandled_target_signal and
#     no [prov] [finalize] finding exists.
# rc: expected tracer returncode.  int for exact match; tuple for any-of;
#     None = rc must just be nonzero.  Negative values are host signals
#     (Python returncode convention); positive values are _exit() codes.
# finding: None or dict(reason=<substring>, is_uaf=<0|1>, count=N)
# fs_status: forkserver tests only — expected child exit status from the
#     driver's 12-byte status record.
# reason: substring required in the [snapshot] [crash] reason field.
# timeout: per-run timeout seconds (forkserver child timeout is separate).
# final_queries: exact `Number of queries` summary expected from symbolic mode.
# final_expr_min: minimum `Number of expressions` summary expected.
TESTS = [
    # --- memcheck-only: no finding, normal exit ---------------------------
    dict(name="t01_double_free", mode="mem", rc=(0, -6, 134),
         verdict="crash", reason="unhandled_target_signal",
         finding=None, note="glibc aborts on real double free"),
    dict(name="t02_small_double_free", mode="mem", rc=(0, -6, 134),
         verdict="crash", finding=None,
         reason="unhandled_target_signal", note="glibc aborts on real double free"),
    dict(name="t03_uaf_stack", mode="mem", rc=(0,), verdict="normal", finding=None),
    dict(name="t04_uaf_heap", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 64, "offset": 0})),
    dict(name="t05_off_oob", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": 8})),
    dict(name="t06_neg_off_oob", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": -1})),
    dict(name="t07_size_ext_oob", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": 1000})),
    dict(name="t08_alloc_zero", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 0, "offset": 0})),
    dict(name="t09_calloc_overflow", mode="mem", rc=(0,), verdict="normal",
         finding=None),
    dict(name="t10_realloc_two_phase", mode="mem", rc=(0,), verdict="normal",
         finding=None),
    dict(name="t11_realloc_shrink", mode="mem", rc=(0,), verdict="normal",
         finding=None),
    dict(name="t12_memcpy_model_oob", mode="sym", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 2, "gen": 1, "size": 8, "offset": 0,
                              "width": 16})),
    dict(name="t13_memset_model_oob", mode="sym", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": 0,
                              "width": 16})),
    dict(name="t14_ea_static", mode="mem", rc=(0,), verdict="normal", finding=None),
    dict(name="t15_ea_dynamic", mode="mem", rc=(0,), verdict="normal", finding=None),
    dict(name="t16_ea_forkserver", mode="fors", rc=(2,), fs_status=0,
         verdict="normal", finding=None),
    dict(name="t17_free_null", mode="mem", rc=(0,), verdict="normal", finding=None),
    dict(name="t18_memchr_unaligned", mode="sym", rc=(0,), verdict="normal",
         finding=None),
    dict(name="t19_plt_child_trace", mode="mem", rc=(0,), verdict="normal",
         finding=None),
    dict(name="t20_concolic_heap_off", mode="sym", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": 1000})),
    dict(name="t21_crash_precedence", mode="sym", rc=(-11, 139), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": 9}),
         reason="unhandled_target_signal",
         note="dual-record: pending finding preserved, real crash wins verdict"),
    dict(name="t22_region_halfopen", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": 0})),
    dict(name="t23_stack_region", mode="mem", rc=(0,), verdict="normal", finding=None),
    dict(name="t24_heap_uninit_read", mode="mem", rc=(0,), verdict="normal",
         finding=None),
    dict(name="t25_global_uninit_read", mode="mem", rc=(0,), verdict="normal",
         finding=None),
    dict(name="t26_use_after_free_gen", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 16, "offset": 0})),
    dict(name="t27_timeout_crash", mode="fors", rc=(2,), fs_status=139,
         verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": 0,
                              "width": 1}),
         note="timeout transport: deferred UAF surfaces as synthetic 139"),
    # --- UNKNOWN-provenance negative cases (no numeric UAF) --------------
    dict(name="t28_unknown_no_uaf", mode="mem", rc=(0,), verdict="normal",
         finding=None,
         note="32-bit write kills tag; freed-address access must not be UAF"),
    dict(name="t29_push_pop_uaf", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                     fields={"obj_id": 1, "gen": 1, "size": 16, "offset": 0}),
         note="push/pop through stack shadow preserves the tag"),
    dict(name="t30_untagged_pop_unknown", mode="mem", rc=(0,), verdict="normal",
         finding=None,
         note="pop from overwritten slot must yield UNKNOWN, not stale tag"),
    dict(name="t31_int_overwrite_clears", mode="mem", rc=(0,), verdict="normal",
         finding=None,
         note="imul overwrite clears the tag; no numeric UAF"),
    dict(name="t32_highbyte_clears", mode="mem", rc=(0,), verdict="normal",
         finding=None,
         note="AH write invalidates the full register; no numeric UAF"),
    dict(name="t33_xchg_swap", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                     fields={"obj_id": 1, "gen": 1, "size": 16, "offset": 0}),
         note="xchg swaps tags with values"),
    dict(name="t34_failed_malloc", mode="mem", rc=(0,), verdict="normal",
         finding=None,
         note="failed malloc creates no object; later allocs unaffected"),
    dict(name="t35_same_addr_realloc", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 64, "offset": 0}),
         note="same-address realloc retires the old identity"),
    dict(name="t36_self_overwrite_load", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": 8,
                              "width": 8}),
         note="load overwriting its own EA base is checked pre-access"),
    dict(name="t37_atomic_rmw", mode="mem", rc=(0,), verdict="normal",
         finding=None,
         note="lock xorq RMW survives memcheck instrumentation (temp-reuse P0)"),
    dict(name="t38_x87_store_semantics", mode="mem", rc=(0,),
         verdict="normal", finding=None),
    dict(name="t39_failed_access_ordering", mode="mem", rc=(-11, 139),
         verdict="crash", reason="unhandled_target_signal", finding=None),
    dict(name="t39b_failed_access_success", mode="mem", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 2, "gen": 1, "width": 8}),
         note="successful crossing load must publish the tagged realloc "
              "identity, not the UNKNOWN fallback"),
    dict(name="t40_thread_inherit", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 16,
                              "offset": 0, "width": 1})),
    dict(name="t41_cross_thread_shadow", mode="mem", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 24,
                              "offset": 0, "width": 1})),
    dict(name="t42_mapping_reuse", mode="mem", rc=(0,),
         verdict="normal", finding=None,
         note="MAP_FIXED file reuse clears same-value stale pointer shadow"),
    dict(name="t43_syscall_output", mode="mem", rc=(0,),
         verdict="normal", finding=None),
    dict(name="t44_simd_overlap", mode="mem", rc=(0,),
         verdict="normal", finding=None),
    dict(name="t45_post_finding_query", mode="sym", rc=(0,),
         verdict="crash", final_queries=1, final_expr_min=1,
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8,
                              "offset": 9, "width": 1})),
]

# Env vars that must always be set: parse_exclude_region_str strchr()s the
# getenv result without a NULL check — all three ranges are required.
BASE_ENV = {
    "BINRADAR_TRACE_FILE": "none",
    "BINRADAR_FORKSERVER_ENABLE": "0",
    "PATCH_RESERVE_RANGE": "0x0-0x0",
    "E9_TRAMPOLINE_RANGE": "0x0-0x0",
    "E9_LOADER_RANGE": "0x0-0x0",
    "BINRADAR_MEMCHECK_ENABLE": "1",
}

# ---------------------------------------------------------------------------
# Log parsing
# ---------------------------------------------------------------------------

def parse_exit_line(out):
    """Return the verdict and optional cursor fields from an exit record."""
    m = re.search(
        r"^\[snapshot\] \[exit\] \[(normal|crash)\]"
        r" \[entrypoint-hit [^\]]+\](.*)$", out, re.MULTILINE)
    if not m:
        return (None, None, None)
    fields = dict(re.findall(r"\[([a-z_]+) ([^\]]+)\]", m.group(2)))
    next_query = fields.get("next_query")
    next_expr = fields.get("next_free_expr")
    return (
        m.group(1),
        int(next_query, 16) if next_query is not None else None,
        int(next_expr, 16) if next_expr is not None else None,
    )


def parse_crash_reason(out):
    m = re.search(r"\[snapshot\] \[crash\] \[hit-count [0-9]+\] \[reason ([^\]]+)", out)
    return m.group(1) if m else None


def parse_findings(out):
    """Parse finding records without rejecting unknown or missing fields."""
    findings = []
    for m in re.finditer(
            r"^\[prov\] \[finalize\] \[finding\](.*)$", out,
            re.MULTILINE):
        findings.append(dict(re.findall(
            r"\[([a-z_]+) ([^\]]+)\]", m.group(1))))
    return findings


def parse_symbolic_counts(out):
    query = re.search(r"^Number of queries: ([0-9]+)$", out, re.MULTILINE)
    expr = re.search(r"^Number of expressions: ([0-9]+)$", out, re.MULTILINE)
    return (
        int(query.group(1)) if query else None,
        int(expr.group(1)) if expr else None,
    )


HEX_FIELDS = {"access_pc", "access_addr", "obj_base", "size",
              "producer_pc", "last_writer", "query_cursor", "expr_cursor"}


def finding_int(finding, field):
    return int(finding[field], 16 if field in HEX_FIELDS else 10)


def rc_ok(rc, expect):
    if expect is None:
        return rc != 0
    if isinstance(expect, tuple):
        return rc in expect
    return rc == expect


# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------

def resolve_entrypoint(guest):
    """main() address from nm — the binary is non-PIE."""
    nm = subprocess.run(["nm", guest], capture_output=True, text=True)
    for line in nm.stdout.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[1] == "T" and parts[2] == "main":
            return "0x" + parts[0]
    raise RuntimeError(f"no 'main' symbol in {guest}")


def run_tracer(cmd, env, timeout):
    return subprocess.run(cmd, env=env, capture_output=True, timeout=timeout)


def run_memcheck(test, guest, qemu, workdir):
    env = dict(os.environ)
    env.update(BASE_ENV)
    env["BINRADAR_ENTRYPOINT"] = resolve_entrypoint(guest)
    env["PLT_INFO_FILE"] = guest + ".plt"
    cmd = [qemu, "-d", "page", guest]
    return run_tracer(cmd, env, test.get("timeout", 30))


def run_solver(solver_bin, env, run_dir, timeout):
    """Start the solver with the shared env; returns the Popen handle."""
    for key in ("EXPR_POOL_SHM_KEY", "QUERY_SHM_KEY", "MUTATION_REQ_SHM_KEY"):
        env[key] = hex(random.getrandbits(32))
    env["SOLVER_TIMEOUT"] = str(int(timeout) + 10)
    env["SYMBOLIC_INJECT_INPUT_MODE"] = "FROM_FILE"
    env["SYMBOLIC_TESTCASE_NAME"] = os.path.join(run_dir, "input")
    with open(env["SYMBOLIC_TESTCASE_NAME"], "w") as f:
        f.write("A")
    os.makedirs(os.path.join(run_dir, "out"), exist_ok=True)
    for b in ("global-bitmap", "context-bitmap", "memory-bitmap"):
        open(os.path.join(run_dir, b), "w").close()
    solver = subprocess.Popen(
        ["stdbuf", "-o0", solver_bin,
         "-i", env["SYMBOLIC_TESTCASE_NAME"],
         "-o", os.path.join(run_dir, "out"),
         "-b", os.path.join(run_dir, "global-bitmap"),
         "-c", os.path.join(run_dir, "context-bitmap"),
         "-m", os.path.join(run_dir, "memory-bitmap")],
        env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        start_new_session=True,
    )
    # The tracer polls shmget for the pools; give the solver time to create
    # them before the tracer starts.
    time.sleep(1.2)
    return solver


def run_symbolic(test, guest, qemu, solver_bin, workdir):
    run_dir = tempfile.mkdtemp(prefix="prov-test-")
    env = dict(os.environ)
    env.update(BASE_ENV)
    env["BINRADAR_ENTRYPOINT"] = resolve_entrypoint(guest)
    env["PLT_INFO_FILE"] = guest + ".plt"
    solver = None
    try:
        solver = run_solver(solver_bin, env, run_dir, test.get("timeout", 30))
        cmd = [qemu, "-symbolic", guest]
        return run_tracer(cmd, env, test.get("timeout", 30))
    finally:
        if solver is not None:
            try:
                solver.terminate()
                solver.wait(timeout=5)
            except (subprocess.TimeoutExpired, ProcessLookupError):
                solver.kill()
        cleanup_shm(env)


def cleanup_shm(env):
    for key in ("EXPR_POOL_SHM_KEY", "QUERY_SHM_KEY", "MUTATION_REQ_SHM_KEY"):
        k = env.get(key)
        if k:
            subprocess.run(["ipcrm", "-M", k], capture_output=True)


def run_forkserver(test, guest, qemu, solver_bin, workdir):
    """Forkserver driver: handshake, one child iteration, close the parent
    pipe. Returns (tracer_rc, child_status, stderr_text)."""
    run_dir = tempfile.mkdtemp(prefix="prov-fs-")
    env = dict(os.environ)
    env.update(BASE_ENV)
    env["BINRADAR_FORKSERVER_ENABLE"] = "1"
    env["BINRADAR_ENTRYPOINT"] = resolve_entrypoint(guest)
    env["PLT_INFO_FILE"] = guest + ".plt"
    env["BINRADAR_FORKSERVER_CHILD_TIMEOUT"] = "4"
    solver = None
    ctrl_r = ctrl_w = stat_r = stat_w = None
    try:
        solver = run_solver(solver_bin, env, run_dir, test.get("timeout", 30))
        ctrl_r, ctrl_w = os.pipe()
        stat_r, stat_w = os.pipe()
        env["BINRADAR_FORKSERVER_CTRL_R"] = str(ctrl_r)
        env["BINRADAR_FORKSERVER_STAT_W"] = str(stat_w)
        os.set_inheritable(ctrl_r, True)
        os.set_inheritable(stat_w, True)
        stderr_path = os.path.join(run_dir, "tracer.stderr")
        stderr_fh = open(stderr_path, "w")
        proc = subprocess.Popen(
            [qemu, "-symbolic", guest],
            env=env, pass_fds=(ctrl_r, stat_w),
            stdout=subprocess.DEVNULL, stderr=stderr_fh,
            start_new_session=True,
        )
        os.close(ctrl_r)
        os.close(stat_w)

        def read_exact(fd, n):
            buf = b""
            while len(buf) < n:
                chunk = os.read(fd, n - len(buf))
                if not chunk:
                    break
                buf += chunk
            return buf

        # Handshake: banner, reply banner ^ 0xffffffff, ack.
        banner = read_exact(stat_r, 4)
        if len(banner) != 4:
            proc.wait(timeout=10)
            raise RuntimeError(
                f"forkserver banner EOF (tracer rc={proc.returncode})")
        os.write(ctrl_w, struct.pack("<I",
                                     struct.unpack("<I", banner)[0] ^ 0xFFFFFFFF))
        ack = read_exact(stat_r, 4)
        if len(ack) != 4:
            proc.wait(timeout=10)
            raise RuntimeError("forkserver ack EOF")

        # One iteration.
        os.write(ctrl_w, struct.pack("<I", 0))  # was_killed
        status = read_exact(stat_r, 12)
        child_status = struct.unpack("<III", status)[0] if len(status) == 12 else -1
        os.write(ctrl_w, struct.pack("<I", 0))  # analyze_result_len
        remaining = read_exact(stat_r, 4)

        os.close(ctrl_w)
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, 9)
            proc.wait(timeout=5)
        stderr_fh.close()
        with open(stderr_path, "r", errors="replace") as f:
            stderr_text = f.read()
        return (proc.returncode, child_status, stderr_text)
    finally:
        if ctrl_w is not None:
            try:
                os.close(ctrl_w)
            except OSError:
                pass
        if solver is not None:
            try:
                solver.terminate()
                solver.wait(timeout=5)
            except (subprocess.TimeoutExpired, ProcessLookupError):
                solver.kill()
        cleanup_shm(env)


def run_test(test, guests_dir, workdir, qemu, solver):
    guest = os.path.join(workdir, test["name"])
    if not os.path.isfile(guest):
        raise FileNotFoundError(f"guest binary missing: {guest} (run 'make guests')")
    if test["mode"] == "mem":
        result = run_memcheck(test, guest, qemu, workdir)
        rc, stderr_text = result.returncode, result.stderr.decode(errors="replace")
        fs_status = None
    elif test["mode"] == "sym":
        result = run_symbolic(test, guest, qemu, solver, workdir)
        rc, stderr_text = result.returncode, result.stderr.decode(errors="replace")
        fs_status = None
    else:
        rc, fs_status, stderr_text = run_forkserver(test, guest, qemu, solver, workdir)

    return (rc, fs_status, stderr_text)


def check(test, rc, fs_status, out):
    problems = []
    if not rc_ok(rc, test.get("rc", (0,))):
        problems.append(f"rc={rc} not in {test.get('rc')}")
    if test["mode"] == "fors":
        want_status = test.get("fs_status")
        if want_status is not None and fs_status != want_status:
            problems.append(f"child status {fs_status} != {want_status}")

    verdict, final_query, final_expr = parse_exit_line(out)
    want_verdict = test["verdict"]
    if verdict != want_verdict:
        problems.append(f"exit verdict {verdict!r} != {want_verdict!r}")
    reason = parse_crash_reason(out)
    if test.get("reason") and reason is None:
        problems.append("missing [snapshot] [crash] reason")
    elif test.get("reason") and test["reason"] not in reason:
        problems.append(f"crash reason {reason!r} != {test['reason']!r}")

    final_queries, final_expressions = parse_symbolic_counts(out)
    if "final_queries" in test and final_queries != test["final_queries"]:
        problems.append(
            f"final query count {final_queries!r} != {test['final_queries']}")
    if ("final_expr_min" in test and
            (final_expressions is None or
             final_expressions < test["final_expr_min"])):
        problems.append(
            f"final expression count {final_expressions!r} < "
            f"{test['final_expr_min']}")

    findings = parse_findings(out)
    want = test.get("finding")
    if want is None:
        if findings:
            problems.append(f"unexpected finding: {findings[0].get('reason', '?')}")
        return problems

    want_count = want.get("count", 1)
    if len(findings) != want_count:
        problems.append(f"finding count {len(findings)} != {want_count}")
    if not findings:
        return problems

    got = findings[0]
    required = {
        "reason", "access_pc", "access_addr", "width", "obj_id", "gen",
        "obj_base", "size", "offset", "producer_pc", "kind",
        "last_writer", "is_uaf", "ea_reg",
    }
    missing = sorted(required - got.keys())
    if missing:
        problems.append("finding missing fields: " + ", ".join(missing))
        return problems

    if want["reason"] not in got["reason"]:
        problems.append(f"finding reason {got['reason']!r} != {want['reason']!r}")
    if finding_int(got, "is_uaf") != want["is_uaf"]:
        problems.append(f"is_uaf {got['is_uaf']} != {want['is_uaf']}")
    for field, want_val in want.get("fields", {}).items():
        if finding_int(got, field) != want_val:
            problems.append(
                f"finding {field} {finding_int(got, field)!r} != {want_val!r}")

    access_pc = finding_int(got, "access_pc")
    access_addr = finding_int(got, "access_addr")
    width = finding_int(got, "width")
    obj_id = finding_int(got, "obj_id")
    obj_base = finding_int(got, "obj_base")
    offset = finding_int(got, "offset")
    if access_pc == 0 or width == 0:
        problems.append("access PC/width must be nonzero")
    if obj_id != 0:
        expected_addr = (obj_base + offset) & ((1 << 64) - 1)
        if access_addr != expected_addr:
            problems.append(
                f"access address {access_addr:#x} != base+offset {expected_addr:#x}")
        for field in ("gen", "obj_base", "producer_pc", "kind",
                      "last_writer"):
            if finding_int(got, field) == 0:
                problems.append(f"tagged finding field {field} is zero")
        if finding_int(got, "ea_reg") < 0:
            problems.append("tagged finding has no EA register")

    query_at_finding = got.get("query_cursor")
    expr_at_finding = got.get("expr_cursor")
    if query_at_finding is not None and final_query is not None:
        if final_query < finding_int(got, "query_cursor"):
            problems.append("final query cursor precedes finding cursor")
    if expr_at_finding is not None and final_expr is not None:
        if final_expr < finding_int(got, "expr_cursor"):
            problems.append("final expression cursor precedes finding cursor")
    return problems


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("guests", help="guests source dir (unused, for CLI parity)")
    ap.add_argument("work", help="work dir with built guests + .plt files")
    ap.add_argument("qemu", help="tracer binary")
    ap.add_argument("solver", help="solver binary")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--test", default=None, help="run only this test name")
    args = ap.parse_args()

    if not os.path.isfile(args.qemu):
        sys.exit(f"tracer binary not found: {args.qemu}")
    if not os.path.isfile(args.solver):
        sys.exit(f"solver binary not found: {args.solver}")

    failures = []
    ran = 0
    for spec in TESTS:
        if args.test and spec["name"] != args.test:
            continue
        ran += 1
        start = time.time()
        try:
            rc, fs_status, out = run_test(spec, args.guests, args.work,
                                          args.qemu, args.solver)
        except Exception as e:  # noqa: BLE001 — per-test isolation
            failures.append(spec)
            print(f"FAIL {spec['name']}: {e}")
            continue
        problems = check(spec, rc, fs_status, out)
        dt = time.time() - start
        if problems:
            failures.append(spec)
            print(f"FAIL {spec['name']} ({dt:.1f}s): " + "; ".join(problems))
            if not args.quiet:
                print(out)
        else:
            print(f"PASS {spec['name']} ({dt:.1f}s)")

    print(f"\n{ran - len(failures)}/{ran} tests passed")
    if failures:
        print("Failed: " + ", ".join(s["name"] for s in failures))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
