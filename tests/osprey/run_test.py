#!/usr/bin/env python3
"""OSPREY in-process analysis test harness.

Runs a small guest under the tracer with BINRADAR_OSPREY_ENABLE=1 in
binradar forkserver mode (patch shm + patch fd). Stage 0 asserts that
known-invalid graphs and injected limits reject atomically, expose no
typed model, retain a generic mutation queue, and reach iteration 2.

The driver replicates the binradar forkserver protocol: handshake,
one baseline iteration, then the iteration-1 analyze barrier which
runs the in-process closure/inference/decode and the model consumer.

Usage:
  make            # build guests + PLT files, run all tests
  make check      # alias for `make`
  make guests     # build guest binaries only
  make plts       # generate PLT files only
  make clean      # remove build products
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
# mode: 'binradar' — forkserver driver with patch shm + BINRADAR_OSPREY_ENABLE
# expect_rows: list of (tag, needle) pairs; a row matches when a line
#     carries `[osprey] [<tag>]` and the needle substring.
# expect_inferred / expect_inferred_max: bounds for `[inferred]` rows.
TESTS = [
    dict(
        name="osprey_deref",
        mode="binradar",
        rc=(2,),  # driver closes the ctrl pipe after 2 iterations
        expect_rows=[
            ("facts", "[samples 1]"),
            ("facts", "[access "),
            ("facts", "[regions "),
            ("graph", "[stage base] [vars "),
            ("graph", "[stage secondary] [vars "),
            ("infer", "[large "),
            ("reject", "[stage infer]"),
        ],
        expect_inferred=0,
        expect_inferred_max=0,
        expect_queue_min=1,
        timeout=60,
    ),
    dict(
        name="osprey_fail_closed",
        guest="osprey_deref",
        mode="binradar",
        rc=(2,),
        env={"BINRADAR_OSPREY_MAX_VARIABLES": "1"},
        expect_rows=[
            ("reject", "[stage closure]"),
        ],
        expect_inferred=0,
        expect_inferred_max=0,
        expect_queue_min=1,
        timeout=60,
    ),
    dict(
        name="t01_regions",
        mode="dump_compare",
        rc=(2,),
        # Canonical rows asserted in the final dump (merged state).
        dump_expect=[
            "region 0 0 ",          # G: site 0
            "region 1 ",            # H_site instances
            "region 2 ",            # S_f frames
            "alloc ",
            "access ",
        ],
        # Structural assertions on the parsed dump (see check_dump).
        dump_assert={
            "global_rows": 1,          # one merged G instance
            "recurse_frames": 4,       # recurse(3) -> 4 live frames
            "same_site_alloc_min": 2,   # two allocations at one site
            "same_base_reuse": True,    # free + realloc at same base
            "realloc_same_base": True,  # realloc success at same base
        },
        timeout=60,
    ),
    dict(
        name="t01_clone",
        mode="binradar",
        rc=(2,),
        expect_rows=[
            ("reject", "[stage merge] [reason unsupported guest execution]"),
        ],
        expect_inferred=0,
        expect_inferred_max=0,
        expect_queue_min=1,
        timeout=60,
    ),
]

BASE_ENV = {
    "BINRADAR_TRACE_FILE": "none",
    "BINRADAR_FORKSERVER_ENABLE": "0",
    "PATCH_RESERVE_RANGE": "0x0-0x0",
    "E9_TRAMPOLINE_RANGE": "0x0-0x0",
    "E9_LOADER_RANGE": "0x0-0x0",
    "BINRADAR_OSPREY_ENABLE": "1",
    "BINRADAR_OSPREY_REPORT_THRESHOLD": "0.2",
}

# ---------------------------------------------------------------------------
# Log parsing
# ---------------------------------------------------------------------------


def has_row(out, tag, needle):
    """True when some line carries `[osprey] [<tag>]` and the needle."""
    return any(
        f"[osprey] [{tag}]" in line and needle in line
        for line in out.splitlines()
    )


def count_inferred(out):
    return len(re.findall(r"\[inferred\]", out))


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def resolve_entrypoint(guest):
    """main() symbol value from nm; elfload adds the PIE load bias."""
    nm = subprocess.run(["nm", guest], capture_output=True, text=True)
    for line in nm.stdout.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[1] == "T" and parts[2] == "main":
            return "0x" + parts[0]
    raise RuntimeError(f"no 'main' symbol in {guest}")


def run_solver(solver_bin, env, run_dir, timeout):
    for key in ("EXPR_POOL_SHM_KEY", "QUERY_SHM_KEY", "BITMAP_SHM_KEY",
                "MUTATION_REQ_SHM_KEY"):
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
    time.sleep(1.2)
    return solver


def cleanup_shm(env):
    for key in ("EXPR_POOL_SHM_KEY", "QUERY_SHM_KEY", "BITMAP_SHM_KEY",
                "MUTATION_REQ_SHM_KEY", "BINRADAR_PATCH_SHM_KEY"):
        k = env.get(key)
        if k:
            subprocess.run(["ipcrm", "-M", k], capture_output=True)


def run_binradar(test, guest, qemu, solver_bin, workdir):
    """Binradar forkserver driver: handshake, baseline iteration, analyze
    barrier, one more iteration, close the parent pipe. Returns
    (tracer_rc, stderr_text)."""
    run_dir = tempfile.mkdtemp(prefix="osprey-test-")
    env = dict(os.environ)
    env.update(BASE_ENV)
    env.update(test.get("env", {}))
    env["BINRADAR_FORKSERVER_ENABLE"] = "1"
    env["BINRADAR_ENTRYPOINT"] = resolve_entrypoint(guest)
    env["PLT_INFO_FILE"] = guest + ".plt"
    env["BINRADAR_FORKSERVER_CHILD_TIMEOUT"] = "4"
    env["BINRADAR_MEMCHECK_ENABLE"] = "1"
    env["BINRADAR_PATCH_CNT"] = "1"
    env["BINRADAR_PATCH_FILTER_FILE"] = ""
    env["BINRADAR_PATCH_SHM_KEY"] = hex(random.getrandbits(32))
    solver = None
    ctrl_r = ctrl_w = stat_r = stat_w = None
    try:
        solver = run_solver(solver_bin, env, run_dir, test.get("timeout", 30))
        ctrl_r, ctrl_w = os.pipe()
        stat_r, stat_w = os.pipe()
        patch_r, patch_w = os.pipe()
        env["BINRADAR_FORKSERVER_CTRL_R"] = str(ctrl_r)
        env["BINRADAR_FORKSERVER_STAT_W"] = str(stat_w)
        env["BINRADAR_PATCH_FD_R"] = str(patch_r)
        os.set_inheritable(ctrl_r, True)
        os.set_inheritable(stat_w, True)
        os.set_inheritable(patch_r, True)
        stderr_path = os.path.join(run_dir, "tracer.stderr")
        stderr_fh = open(stderr_path, "w")
        proc = subprocess.Popen(
            [qemu, "-symbolic", guest],
            env=env, pass_fds=(ctrl_r, stat_w, patch_r),
            stdout=subprocess.DEVNULL, stderr=stderr_fh,
            start_new_session=True,
        )
        os.close(ctrl_r)
        os.close(stat_w)
        os.close(patch_r)
        os.close(patch_w)

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

        # Baseline iteration.
        os.write(ctrl_w, struct.pack("<I", 0))  # was_killed
        status = read_exact(stat_r, 12)
        if len(status) != 12:
            raise RuntimeError("baseline status EOF")
        os.write(ctrl_w, struct.pack("<I", 0))  # analyze_result_len
        remaining = read_exact(stat_r, 4)
        if len(remaining) != 4:
            raise RuntimeError("baseline remaining EOF")

        # Second iteration (after the iter-1 analyze barrier).
        os.write(ctrl_w, struct.pack("<I", 0))
        status2 = read_exact(stat_r, 12)
        if len(status2) != 12:
            raise RuntimeError("second status EOF")
        os.write(ctrl_w, struct.pack("<I", 0))
        remaining2 = read_exact(stat_r, 4)

        os.close(ctrl_w)
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, 9)
            proc.wait(timeout=5)
        stderr_fh.close()
        with open(stderr_path, "r", errors="replace") as f:
            stderr_text = f.read()
        return (proc.returncode, stderr_text)
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


def run_test(test, workdir, qemu, solver):
    guest = os.path.join(workdir, test.get("guest", test["name"]))
    if not os.path.isfile(guest):
        return (None, f"guest binary missing: {guest} (run 'make guests')")
    if not os.path.isfile(guest + ".plt"):
        return (None, f"plt file missing: {guest}.plt (run 'make plts')")
    return run_binradar(test, guest, qemu, solver, workdir)


def run_dump_compare(test, workdir, qemu, solver):
    """Stage-1 canonical-dump gate: run the guest twice with
    BINRADAR_OSPREY_DUMP_FILE set, require byte-identical dumps (PIE
    determinism / ASLR invariance), then assert the expected canonical
    rows.  Returns (tracer_rc, stderr_text)."""
    guest = os.path.join(workdir, test.get("guest", test["name"]))
    if not os.path.isfile(guest):
        return (None, f"guest binary missing: {guest} (run 'make guests')")
    if not os.path.isfile(guest + ".plt"):
        return (None, f"plt file missing: {guest}.plt (run 'make plts')")
    dumps = []
    outs = []
    rcs = []
    for i in range(2):
        dump_path = os.path.join(workdir, f"t01_dump_{i}.txt")
        try:
            os.unlink(dump_path)
        except OSError:
            pass
        spec = dict(test)
        spec["env"] = dict(test.get("env", {}))
        spec["env"]["BINRADAR_OSPREY_DUMP_FILE"] = dump_path
        rc, out = run_binradar(spec, guest, qemu, solver, workdir)
        rcs.append(rc)
        outs.append(out)
        if not os.path.isfile(dump_path):
            return (rc, out + f"\nmissing dump file: {dump_path}")
        with open(dump_path, "r", errors="replace") as f:
            dumps.append(f.read())
    if dumps[0] != dumps[1]:
        return (rcs[-1], outs[0] + "\nDUMP MISMATCH between runs")
    problems = []
    for needle in test.get("dump_expect", []):
        if needle not in dumps[0]:
            problems.append(f"dump missing row {needle!r}")
    if problems:
        return (rcs[-1], outs[0] + "\n" + "\n".join(problems))
    problems = check_dump(test, dumps[0])
    if problems:
        return (rcs[-1], outs[0] + "\n" + "\n".join(problems))
    if rcs[0] != rcs[1]:
        return (rcs[-1], outs[0] +
                f"\ntracer return codes differ: {rcs[0]} != {rcs[1]}")
    return (rcs[-1], outs[0])


def check_dump(test, dump):
    """Structural assertions on the canonical dump (Stage-1 gate)."""
    want = test.get("dump_assert", {})
    if not want:
        return []
    problems = []
    regions = [ln.split() for ln in dump.splitlines() if ln.startswith("region ")]
    globals_rows = [r for r in regions if r[1] == "0"]
    heap_rows = [r for r in regions if r[1] == "1"]
    stack_rows = [r for r in regions if r[1] == "2"]

    if "global_rows" in want and len(globals_rows) != want["global_rows"]:
        problems.append(f"global rows {len(globals_rows)} != {want['global_rows']}")

    if "recurse_frames" in want:
        # deepest recursion: max count of stack rows sharing one site
        from collections import Counter
        sites = Counter(r[2] for r in stack_rows)
        deepest = max(sites.values()) if sites else 0
        if deepest < want["recurse_frames"]:
            problems.append(
                f"deepest frame site depth {deepest} < {want['recurse_frames']}")

    if "same_site_alloc_min" in want:
        from collections import Counter
        sites = Counter(r[2] for r in heap_rows)
        max_site = max(sites.values()) if sites else 0
        if max_site < want["same_site_alloc_min"]:
            problems.append(
                f"max allocs at one site {max_site} < {want['same_site_alloc_min']}")

    if want.get("same_base_reuse"):
        raw_classes = Counter(r[4] for r in heap_rows)
        reused = [b for b, n in raw_classes.items() if n >= 2]
        if not reused:
            problems.append("no same-base reuse observed")

    if want.get("realloc_same_base"):
        # realloc success: two heap instances at the same base with
        # different extents (16 -> 64)
        from collections import defaultdict
        by_base = defaultdict(set)
        for r in heap_rows:
            by_base[r[4]].add(r[5])
        if not any(len(exts) >= 2 for exts in by_base.values()):
            problems.append("no realloc same-base extent change observed")
    return problems


def check(test, rc, out):
    problems = []
    if rc != test.get("rc", (0,)) and rc not in (
            test.get("rc", (0,)) if isinstance(test.get("rc"), tuple) else ()):
        problems.append(f"rc={rc} not in {test.get('rc')}")
    for tag, needle in test.get("expect_rows", []):
        if not has_row(out, tag, needle):
            problems.append(f"missing row [osprey] [{tag}] {needle}")
    want = test.get("expect_inferred", 0)
    got = count_inferred(out)
    if got < want:
        problems.append(f"[inferred] rows {got} < {want}")
    max_inferred = test.get("expect_inferred_max")
    if max_inferred is not None and got > max_inferred:
        problems.append(f"[inferred] rows {got} > {max_inferred}")
    queue_min = test.get("expect_queue_min")
    if queue_min is not None:
        lengths = [int(n) for n in re.findall(
            r"\[analyze\] \[queue\] \[len (\d+)\]", out)]
        if not lengths or max(lengths) < queue_min:
            problems.append(
                f"mutation queue max {max(lengths) if lengths else 'missing'} "
                f"< {queue_min}")
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

    failures: list[str] = []
    ran = 0
    for spec in TESTS:
        if args.test and spec["name"] != args.test:
            continue
        ran += 1
        start = time.time()
        try:
            if spec.get("mode") == "dump_compare":
                rc, out = run_dump_compare(spec, args.work, args.qemu,
                                           args.solver)
            else:
                rc, out = run_test(spec, args.work, args.qemu, args.solver)
            if rc is None:
                problems = [out]
            else:
                problems = check(spec, rc, out)
        except Exception as e:  # noqa: BLE001 — per-test isolation
            failures.append(str(spec["name"]))
            print(f"FAIL {spec['name']}: {e}")
            continue
        dt = time.time() - start
        if problems:
            failures.append(str(spec["name"]))
            print(f"FAIL {spec['name']} ({dt:.1f}s): " + "; ".join(problems))
            if not args.quiet:
                print(out)
        else:
            print(f"PASS {spec['name']} ({dt:.1f}s)")

    print(f"\n{ran - len(failures)}/{ran} tests passed")
    if failures:
        print("Failed: " + ", ".join(failures))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
