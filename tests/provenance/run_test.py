#!/usr/bin/env python3
"""Provenance (pointer-analysis / memcheck) test harness runner.

Runs each guest under the tracer in the mode the test requires and asserts
on the structured `[prov]` / `[snapshot]` / `[forkserver]` stderr log lines.

Modes
-----
memcheck   : plain tracer (-d page), BINRADAR_MEMCHECK_ENABLE=1, no solver.
             Covers allocation-lifecycle / tag-transfer / region tests.
symbolic   : -symbolic + NO_EXTERNAL_SOLVER=1. The tracer keeps the
             expression/query data structures but backs them with process-local
             memory, so libc models (memcpy/memset/memchr) and deferred
             continuation tests need no solver process.
forkserver : -symbolic + NO_EXTERNAL_SOLVER=1 + forkserver pipes. The driver
             performs the handshake and runs one child iteration, then closes
             the ctrl pipe (tracer exits 2 on EOF).

Invocation (see Makefile):
    run_test.py GUESTS WORK QEMU [--quiet]

Exit status: 0 if every test passes, 1 otherwise.
"""

import argparse
import ctypes
import os
import random
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import time
from typing import Any

ROOT = os.path.realpath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "fuzzolic"))
import binradar_evidence


HANDSHAKE_EXPECTED = 0x41464C03
# Mirrors tracer/linux-user/binradar-forkserver.h (protocol v4 enum table).
STOP_CONTINUE = 0
STOP_EXHAUSTED = 1
STOP_BASELINE_UNAVAILABLE = 2
STOP_FAILURE_LIMIT = 3
STOP_RESOURCE_FAILURE = 4
ATTEMPT_COMPLETED = 0
ATTEMPT_NO_OBSERVATION = 1
ATTEMPT_UNUSABLE_EXIT = 2
ATTEMPT_TIMEOUT = 3

STOP_NAMES = {
    STOP_CONTINUE: "continue",
    STOP_EXHAUSTED: "exhausted",
    STOP_BASELINE_UNAVAILABLE: "baseline-unavailable",
    STOP_FAILURE_LIMIT: "failure-limit",
    STOP_RESOURCE_FAILURE: "resource-failure",
}
LOCAL_SOLVER_MAPPING_SIZES = {
    "expression pool": 8 * 1024 * 1024 * 32,
    "query queue": 1024 * 1024 * 24,
}

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
# Forkserver v4 returns one fixed 20-byte attempt summary; detailed child
# outcomes are also verified from the structured tracer log.
# reason: substring required in the [snapshot] [crash] reason field.
# timeout: per-run timeout seconds (forkserver child timeout is separate).
# final_queries: exact `Number of queries` summary expected from symbolic mode.
# final_expr_min: minimum `Number of expressions` summary expected.
# meta: dict of exact structured producer/writer assertions for the first
#     finding.  Keys: producer_kind (int), producer_pc, last_writer,
#     access_pc, ea_reg (int).  PC values are guest symbol names resolved
#     with nm from the built ELF — never hard-coded absolute addresses.
TESTS: list[dict[str, Any]] = [
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
    dict(name="t16_ea_forkserver", mode="fors", rc=(0,),
         verdict="normal", finding=None, check_local_solver_mapping=True,
         note="standalone solver pool and queue use shared mappings required "
              "for forkserver child publication"),
    dict(name="t17_free_null", mode="mem", rc=(0,), verdict="normal", finding=None),
    dict(name="t18_memchr_unaligned", mode="sym", rc=(0,), verdict="normal",
         finding=None),
    dict(name="t19_plt_child_trace", mode="mem", rc=(0,), verdict="normal",
         finding=None),
    dict(name="t20_concolic_heap_off", mode="sym", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": 1000}),
         fault_reference=dict(valid="true", source="provenance-access")),
    dict(name="t21_crash_precedence", mode="sym", rc=(-11, 139), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": 9}),
         reason="unhandled_target_signal",
         fault_reference=dict(valid="true", source="guest-signal",
                              nonzero=True),
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
    dict(name="t27_timeout_crash", mode="fors", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": 0,
                              "width": 1}),
         fault_reference=dict(valid="true", source="provenance-access"),
         note="timeout transport: deferred UAF surfaces as synthetic 139"),
    dict(name="t79_forkserver_abort", mode="fors", rc=(0,),
         verdict="crash", fs_binradar=True, fs_abort_count=3,
         fs_child_timeout=3, timeout=120,
         fs_stop="failure-limit", fs_attempts=3,
         fs_attempt_result=ATTEMPT_NO_OBSERVATION, fs_min_discarded=2,
         fs_discard_reason="no-observation",
         finding=dict(reason="heap-use-after-free", is_uaf=1, count=3,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": 0,
                              "width": 1}),
         note="a hanging guest costs one deadline-killed child per attempt: "
              "each attempt is still discarded and consumes exactly one plan "
              "(remaining 2 -> 1 -> 0) instead of ending the sweep at the "
              "first kill, and the consecutive-bad-attempt limit then stops "
              "the tracer"),
    dict(name="t82_unusable_attempt_recovery", mode="fors", rc=(2,),
         verdict=None, fs_binradar=True, fs_patch_cnt=3, timeout=300,
         fs_max_attempts=8, fs_stop="continue", fs_min_attempts=8,
         fs_min_discarded=1, fs_discard_reason="no-observation",
         allow_findings=True,
         note="the driver stops after its own bounded attempt budget, not "
              "because the tracer ended the sweep: every mutation plan for "
              "this guest diverts control before the patch site, so the "
              "attempts are discarded as ordinary no-observation misses "
              "while the queue keeps advancing.  That proves a discard does "
              "not consume the queue; a later *committing* attempt is proven "
              "by the real subject run recorded in the fix plan's P2 audit, "
              "which the synthetic 8-byte mod target here cannot force"),
    dict(name="t83_final_discarded_plan", 
         guest="t82_unusable_attempt_recovery",
         mode="fors", rc=(0,), verdict=None, fs_binradar=True,
         fs_patch_cnt=3, fs_abort_count=0,   # 0 disables the bad-attempt limit
         fs_max_attempts=400, fs_stop="exhausted", fs_remaining=0,
         fs_attempt_result=ATTEMPT_NO_OBSERVATION, fs_committed=1,
         fs_only_no_observation_discards=True, fs_evidence_attempts=(1,),
         fs_min_discarded=1, fs_discard_reason="no-observation",
         allow_findings=True, timeout=900,
         note="every plan for this guest is discarded, so the LAST queued "
              "plan is discarded too: the sweep ends `exhausted` with "
              "remaining 0, one committed baseline frame and no mutation "
              "frame.  This is the real terminal-discard case; the reducer "
              "must report it partial, never complete"),
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
         note="successful crossing load promotes fallback to tagged "
              "realloc identity"),
    dict(name="t46_ea_tagged_promotion", mode="mem", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 24,
                              "offset": 24, "width": 8}),
         note="constant-displacement EA promotes fallback to tagged "
              "malloc identity"),
    dict(name="t47_ea_index_scale", mode="mem", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 16,
                              "offset": 12, "width": 8}),
         note="verified semantic index fold keeps the tagged identity"),
    dict(name="t47_ea_seg_override", mode="sym", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 0, "gen": 0, "width": 8}),
         note="segment override suppresses identity, keeps symbolic fallback"),
    dict(name="t47_ea_addr32", mode="sym", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 0, "gen": 0, "width": 8}),
         note="addr32 truncation suppresses identity, keeps symbolic fallback"),
    dict(name="t47_ea_negative_disp", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 16,
                              "offset": -1, "width": 1}),
         note="negative displacement uses wrapping target-width EA arithmetic"),
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
                              "offset": 9, "width": 1}),
         cursors=dict(query_after=True, expr_after=True),
         note="post-finding branch query survives and advances the exit "
              "cursors strictly past the finding-time cursors"),
    dict(name="t45_compact_fault_reference", guest="t45_post_finding_query",
         mode="fors", rc=(2,), verdict="crash", fs_binradar=True,
         fs_patch_cnt=1, compact_fault_reference=True, allow_findings=True,
         fs_max_attempts=2, timeout=120, fs_compaction_only=True,
         fault_reference=dict(valid="true", source="provenance-access"),
         note="a real forkserver child publishes its deferred access PC in "
              "compact v2 evidence; the fixture stops once the baseline "
              "attempt is committed instead of draining 486 mutation plans"),
    dict(name="t48_sticky_first_finding", mode="mem", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 2, "gen": 1, "width": 8}),
         note="first tagged finding is sticky: a later tagged UAF at a "
              "different address must not displace it"),
    dict(name="t49_sticky_unknown_fallback", mode="mem", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 0, "gen": 0, "width": 8}),
         note="UNKNOWN fallback is sticky: a later tagged UAF at a "
              "different address must not displace it"),
    dict(name="t50_strcpy_model_oob", mode="sym", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8,
                              "offset": 0, "width": 17}),
         note="strcpy checks the full destination and source via RSI"),
    dict(name="t51_strncpy_model_padding_oob", mode="sym", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8,
                              "offset": 0, "width": 16}),
         note="strncpy checks and invalidates its full n-byte output"),
    dict(name="t52_strcpy_fault_ordering", mode="sym", rc=(-11, 139),
         verdict="crash", reason="unhandled_target_signal", finding=None,
         note="failed strcpy destination preflight leaves the real fault"),
    dict(name="t53_memcpy_fault_ordering", mode="sym", rc=(-11, 139),
         verdict="crash", reason="unhandled_target_signal", finding=None,
         note="failed memcpy source preflight leaves the real fault"),
    dict(name="t54_zero_length_models", mode="sym", rc=(0,),
         verdict="normal", finding=None,
         note="bounded zero-length models access no pointer arguments"),
    dict(name="t55_strcmp_exact_ranges", mode="sym", rc=(0,),
         verdict="normal", finding=None,
         note="strcmp checks each string only through its own NUL"),
    dict(name="t56_memmove_overlap_symbolic", mode="sym", rc=(0,),
         verdict="normal", finding=None, final_queries=1, final_expr_min=1,
         note="lower-address overlapping memmove preserves the symbolic "
              "source byte across a 64-KiB shadow-leaf boundary"),
    # --- Phase 4: exact syscall output invalidation ---------------------
    dict(name="t57_syscall_failed_stat_tag_intact", mode="mem", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 16,
                              "offset": 0, "width": 1}),
         note="failed stat() must not invalidate the pointer tag in its "
              "output buffer (old code invalidated unconditionally)"),
    dict(name="t58_stat_adjacent_untouched", mode="mem", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 16,
                              "offset": 0, "width": 1}),
         note="stat invalidates exactly sizeof(target_stat)=144, not a "
              "256-byte window: tag at buf+144 survives"),
    dict(name="t59_partial_readv_exact", mode="mem", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 16,
                              "offset": 0, "width": 1}),
         note="partial readv invalidates only the returned bytes: tag in "
              "the second iovec survives"),
    dict(name="t60_zero_len_recvfrom_metadata", mode="mem", rc=(0,),
         verdict="crash", no_consistency=True,
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 16,
                              "offset": 0, "width": 1}),
         note="zero-length recvfrom writes no payload (tag survives) but "
              "still writes the addrlen word (tag invalidated); debug run "
              "must show no consistency-mismatch"),
    dict(name="t61_recvfrom_addr_addrlen", mode="mem", rc=(0,),
         verdict="crash", no_consistency=True,
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 16,
                              "offset": 0, "width": 1}),
         note="recvfrom invalidates exactly ret payload bytes, the "
              "returned sockaddr, and the addrlen word; tags beyond each "
              "range survive"),
    dict(name="t62_recvmsg_payload_name_control", mode="mem", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 16,
                              "offset": 0, "width": 1}),
         note="recvmsg invalidates exactly the payload iovecs, msg_name, "
              "and control data; tags beyond each range survive"),
    dict(name="t63_recvmsg_header_fields", mode="mem", rc=(0,),
         verdict="crash", no_consistency=True,
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 16,
                              "offset": 0, "width": 1}),
         note="recvmsg invalidates the returned msg_namelen and msg_flags "
              "header fields; debug run must show no consistency-mismatch"),
    dict(name="t64_gettimeofday_timezone_untouched", mode="mem", rc=(0,),
         verdict="crash",
         finding=dict(reason="heap-use-after-free", is_uaf=1,
                      fields={"obj_id": 1, "gen": 1, "size": 16,
                              "offset": 0, "width": 1}),
         note="QEMU gettimeofday writes timeval only; the obsolete timezone "
              "argument must retain its pointer tag"),
    dict(name="t65_futex_wake_op_output", mode="mem", rc=(0,),
         verdict="normal", finding=None, no_consistency=True,
         note="successful FUTEX_WAKE_OP invalidates the 32-bit uaddr2 word "
              "without relying on load-time consistency repair"),
    dict(name="t66_readv_iovec_overlap", mode="mem", rc=(0,),
         verdict="normal", finding=None,
         note="readv invalidates from the pre-syscall locked vector when an "
              "earlier output overwrites a later guest iovec descriptor"),
    dict(name="t67_recvmsg_partial_error", mode="mem", rc=(0,),
         verdict="normal", finding=None,
         note="recvmsg payload invalidation commits before a later control "
              "copyout EFAULT returns an error to the guest"),
]

# Env vars that must always be set for the tracer runs.
BASE_ENV = {
    "BINRADAR_TRACE_FILE": "none",
    "BINRADAR_FORKSERVER_ENABLE": "0",
    "E9_EXCLUDE_RANGES": "",
    "BINRADAR_MEMCHECK_ENABLE": "1",
}

# ---------------------------------------------------------------------------
# Phase 5: store-width regressions and exact producer metadata
# ---------------------------------------------------------------------------
# t68-t73: each guest stores the freed pointer's own bytes back into the
# shadow slot unchanged, then reloads the slot with an 8-byte load.  A
# surviving shadow entry would pass the load-time value-consistency check
# and restore the tag, making the freed-address access a UAF finding.  Only
# the store's overlap invalidation can make the reload UNKNOWN, so these
# tests prove shadow removal, not merely that concrete bytes changed.
# t74-t78: named guest labels (prov_*_site) are resolved with nm; the
# finding's producer_kind, producer_pc, last_writer, access_pc, and ea_reg
# must match the exact instruction that created/transferred the tag.
PHASE5_TESTS: list[dict[str, Any]] = [
    dict(name="t68_store_width_1", mode="mem", rc=(0,), verdict="normal",
         finding=None,
         note="1-byte store of identical pointer bytes removes the shadow"),
    dict(name="t69_store_width_2", mode="mem", rc=(0,), verdict="normal",
         finding=None,
         note="2-byte store of identical pointer bytes removes the shadow"),
    dict(name="t70_store_width_4", mode="mem", rc=(0,), verdict="normal",
         finding=None,
         note="4-byte store of identical pointer bytes removes the shadow"),
    dict(name="t71_store_unaligned_8", mode="mem", rc=(0,), verdict="normal",
         finding=None,
         note="unaligned 8-byte store of identical pointer bytes removes "
              "the shadow"),
    dict(name="t72_store_width_16", mode="mem", rc=(0,), verdict="normal",
         finding=None,
         note="16-byte SSE store of identical pointer bytes removes the "
              "shadow across two pointer slots"),
    dict(name="t73_store_atomic", mode="mem", rc=(0,), verdict="normal",
         finding=None,
         note="lock-prefixed atomic store of identical pointer bytes removes "
              "the shadow"),
    dict(name="t74_producer_malloc", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8,
                              "offset": 8, "width": 1}),
         meta=dict(producer_kind=1, producer_pc="prov_alloc_site",
                   last_writer="prov_alloc_site",
                   access_pc="prov_access_site", ea_reg=0),
         note="malloc-return tag: producer is the call return site"),
    dict(name="t75_producer_mov", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8,
                              "offset": 8, "width": 1}),
         meta=dict(producer_kind=4, producer_pc="prov_mov_site",
                   last_writer="prov_mov_site",
                   access_pc="prov_access_site", ea_reg=1),
         note="mov transfer: producer is the mov instruction"),
    dict(name="t76_producer_add", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8,
                              "offset": 8, "width": 1}),
         meta=dict(producer_kind=6, producer_pc="prov_add_site",
                   last_writer="prov_add_site",
                   access_pc="prov_access_site", ea_reg=3),
         note="add-immediate fold: producer is the add instruction"),
    dict(name="t77_producer_pop", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8,
                              "offset": 8, "width": 1}),
         meta=dict(producer_kind=8, producer_pc="prov_pop_site",
                   last_writer="prov_pop_site",
                   access_pc="prov_access_site", ea_reg=1),
         note="stack-reload: producer is the pop instruction"),
    dict(name="t78_producer_calloc", mode="mem", rc=(0,), verdict="crash",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8,
                              "offset": 8, "width": 1}),
         meta=dict(producer_kind=2, producer_pc="prov_alloc_site",
                   last_writer="prov_alloc_site",
                   access_pc="prov_access_site", ea_reg=0),
         note="calloc-return tag: producer is the call return site"),
]
TESTS += PHASE5_TESTS

# ---------------------------------------------------------------------------
# t80: pre-entry XMM memory access under semantic-event instrumentation
# ---------------------------------------------------------------------------
# The guest's constructor runs before main (the forkserver entrypoint) and
# performs `movss mem -> xmm0 -> mem` plus an XMM register copy.  With
# semantic events active (memcheck or OSPREY) the translator inserts a
# helper call between the guest load and its XMM store; the symbolic engine
# used to match that pair by physical adjacency and aborted during
# translation, so the forkserver banner was never written and the driver
# saw a banner EOF.  This must now handshake, run the child to a normal
# exit, and report no finding.
PHASE6_TESTS: list[dict[str, Any]] = [
    dict(name="t80_xmm_preentry_forkserver", mode="fors", rc=(0,),
         verdict="normal", finding=None,
         note="pre-entry movss under sem-events: banner instead of abort"),
]
TESTS += PHASE6_TESTS

# ---------------------------------------------------------------------------
# t81: PLT model table identity across artifact-named executions
# ---------------------------------------------------------------------------
# PLT_INFO_FILE rows are keyed by the basename of the executable the table
# was generated from, and BinRadar executes derived artifacts of that
# executable (<binary>.brpatched / <binary>.brcached) whose PLT layout is
# identical.  Comparing raw basenames registered no model for an artifact
# run, so the allocator hooks vanished and a real heap violation reported a
# normal exit.  Generate the table from a `.orig` copy, then execute the
# `.brpatched` copy: the finding must still be published.
PHASE7_TESTS: list[dict[str, Any]] = [
    dict(name="t81_plt_image_identity", mode="mem", rc=(0,),
         verdict="crash", artifact_suffix=".brpatched",
         plt_source_suffix=".orig",
         finding=dict(reason="heap-buffer-overflow", is_uaf=0,
                      fields={"obj_id": 1, "gen": 1, "size": 8, "offset": 8}),
         note="artifact-suffixed execution still resolves the PLT model "
              "table generated for the .orig executable"),
]
TESTS += PHASE7_TESTS

# ---------------------------------------------------------------------------
# Log parsing
# ---------------------------------------------------------------------------

def parse_exit_line(out):
    """Return the verdict and stable final query/expression indices."""
    exit_match = re.search(
        r"^\[snapshot\] \[exit\] \[(normal|crash)\]"
        r" \[entrypoint-hit [^\]]+\]$", out, re.MULTILINE)
    if not exit_match:
        return (None, None, None)
    cursor_match = re.search(
        r"^\[snapshot\] \[cursors\] \[query_cursor (-?[0-9]+)\]"
        r" \[expr_cursor (-?[0-9]+)\]$", out, re.MULTILINE)
    return (
        exit_match.group(1),
        int(cursor_match.group(1)) if cursor_match else None,
        int(cursor_match.group(2)) if cursor_match else None,
    )


def parse_crash_reason(out):
    m = re.search(r"\[snapshot\] \[crash\] \[hit-count [0-9]+\] \[reason ([^\]]+)", out)
    return m.group(1) if m else None


def parse_fault_references(out):
    return [
        dict(valid=valid, source=source, address=int(address, 16))
        for valid, source, address in re.findall(
            r"^\[snapshot\] \[fault-reference\] \[version 2\] "
            r"\[valid (true|false)\] \[source ([^\]]+)\] "
            r"\[address ([0-9a-fA-F]+)\]$", out, re.MULTILINE)
    ]


def parse_crash_fault_addresses(out):
    return [
        int(address, 16)
        for address in re.findall(
            r"^\[snapshot\] \[crash\] \[hit-count [0-9]+\] .*"
            r"\[fault_addr ([0-9a-fA-F]+)\] \[host_fault_addr [^\]]+\]$",
            out, re.MULTILINE)
    ]


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
              "producer_pc", "last_writer"}


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


def resolve_symbols(guest, names):
    """Resolve named guest symbols to absolute addresses via nm.

    The Phase 5 metadata tests express their PC contracts as named labels
    (prov_*_site) in the guest source; the runner resolves them from the
    built ELF so no hard-coded absolute PC can silently drift out of sync
    with the guest code.
    """
    nm = subprocess.run(["nm", guest], capture_output=True, text=True)
    addrs = {}
    for line in nm.stdout.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[2] in names:
            addrs[parts[2]] = int(parts[0], 16)
    missing = sorted(names - addrs.keys())
    if missing:
        raise RuntimeError(f"missing symbols in {guest}: {', '.join(missing)}")
    return addrs


def run_tracer(cmd, env, timeout):
    return subprocess.run(cmd, env=env, capture_output=True, timeout=timeout)


def run_memcheck(test, guest, qemu, workdir):
    env = dict(os.environ)
    env.update(BASE_ENV)
    env["BINRADAR_PROBE_FILE"] = test.get("probe_file", "")
    env["BINRADAR_ENTRYPOINT"] = resolve_entrypoint(guest)
    env["PLT_INFO_FILE"] = guest + ".plt"
    source_suffix = test.get("plt_source_suffix")
    if source_suffix:
        source = guest + source_suffix
        shutil.copyfile(guest, source)
        env["PLT_INFO_FILE"] = source + ".plt"
        subprocess.run([sys.executable,
                        os.path.join(os.path.dirname(__file__), "gen_plt.py"),
                        "-o", env["PLT_INFO_FILE"], source], check=True)
    if test.get("no_consistency"):
        # Phase 4: changed-byte syscall outputs must be invalidated by the
        # hook, not silently dropped by the load-time value-consistency
        # check.  With debug logging on, a missing hook shows up as a
        # `[prov] [consistency]` line; the check() below rejects it.
        env["BINRADAR_PROVENANCE_DEBUG"] = "1"
    # Execute under a name carrying a pipeline artifact suffix while
    # PLT_INFO_FILE names the .orig binary: exactly how BinRadar runs
    # <binary>.brpatched/.brcached against a table generated from
    # <binary>.orig.  Copy through a temporary file so the suffixed
    # executable is never a partially written binary.
    suffix = test.get("artifact_suffix")
    binary = guest
    if suffix:
        binary = guest + suffix
        temporary = binary + ".tmp"
        shutil.copyfile(guest, temporary)
        os.chmod(temporary, 0o755)
        os.replace(temporary, binary)
    cmd = [qemu, "-d", "page", binary]
    return run_tracer(cmd, env, test.get("timeout", 30))


def prepare_symbolic_env(env, run_dir):
    """Configure symbolic input while leaving the solver transport local."""
    env["NO_EXTERNAL_SOLVER"] = "1"
    for key in ("EXPR_POOL_SHM_KEY", "QUERY_SHM_KEY", "BITMAP_SHM_KEY",
                "MUTATION_REQ_SHM_KEY"):
        env.pop(key, None)
    env["SYMBOLIC_INJECT_INPUT_MODE"] = "FROM_FILE"
    env["SYMBOLIC_TESTCASE_NAME"] = os.path.join(run_dir, "input")
    with open(env["SYMBOLIC_TESTCASE_NAME"], "w") as f:
        f.write("A")


def run_symbolic(test, guest, qemu, workdir):
    run_dir = tempfile.mkdtemp(prefix="prov-test-")
    env = dict(os.environ)
    env.update(BASE_ENV)
    env["BINRADAR_PROBE_FILE"] = test.get("probe_file", "")
    env["BINRADAR_ENTRYPOINT"] = resolve_entrypoint(guest)
    env["PLT_INFO_FILE"] = guest + ".plt"
    prepare_symbolic_env(env, run_dir)
    cmd = [qemu, "-symbolic", guest]
    return run_tracer(cmd, env, test.get("timeout", 30))


def cleanup_shm(env):
    for key in ("EXPR_POOL_SHM_KEY", "QUERY_SHM_KEY", "MUTATION_REQ_SHM_KEY",
                "BINRADAR_PATCH_SHM_KEY"):
        k = env.get(key)
        if k:
            subprocess.run(["ipcrm", "-M", k], capture_output=True)


def check_local_solver_mapping(pid):
    """Require all local solver buffers to match shm fork semantics."""
    shared_sizes = []
    with open(f"/proc/{pid}/maps", encoding="ascii") as maps_file:
        for line in maps_file:
            fields = line.split()
            permissions = fields[1]
            if len(permissions) < 4 or permissions[3] != "s":
                continue
            start_text, end_text = fields[0].split("-", 1)
            shared_sizes.append(int(end_text, 16) - int(start_text, 16))
    missing = [name for name, size in LOCAL_SOLVER_MAPPING_SIZES.items()
               if size not in shared_sizes]
    if missing:
        raise RuntimeError(
            "NO_EXTERNAL_SOLVER mappings are not shared: " +
            ", ".join(missing) + "; observed sizes=" +
            ",".join(hex(size) for size in sorted(shared_sizes)))


def _summarize(summaries):
    """Reduce raw protocol-v4 replies into the fields ``check`` asserts on."""
    if not summaries:
        return None
    attempts = len(summaries)
    results = [row[3] for row in summaries]
    return {
        "attempts": attempts,
        "initial_remaining": summaries[0][2],
        "attempt_result": results[-1],
        "stop_reason": summaries[-1][4],
        "stop_name": STOP_NAMES.get(summaries[-1][4], "invalid"),
        "remaining": summaries[-1][2],
        "committed": results.count(ATTEMPT_COMPLETED),
        "discarded": sum(1 for result in results
                         if result != ATTEMPT_COMPLETED),
        "no_observation": results.count(ATTEMPT_NO_OBSERVATION),
        "timeouts": results.count(ATTEMPT_TIMEOUT),
        "unusable": results.count(ATTEMPT_UNUSABLE_EXIT),
    }


def run_forkserver(test, guest, qemu, workdir):
    """Forkserver driver: handshake, iterate children until the plan ends
    (remaining == 0), close the parent pipe.  With ``fs_binradar`` the
    driver also sets up the binradar patch shm/fd so the forkserver runs
    its binradar-mode loop (patch-id iteration, child-timeout abort).
    Returns (tracer_rc, None, stderr_text, evidence); outcomes live in
    stderr rows and optional production-decoded compact evidence."""
    run_dir = tempfile.mkdtemp(prefix="prov-fs-")
    env = dict(os.environ)
    env.update(BASE_ENV)
    env["BINRADAR_PROBE_FILE"] = test.get("probe_file", "")
    env["BINRADAR_FORKSERVER_ENABLE"] = "1"
    env["BINRADAR_ENTRYPOINT"] = resolve_entrypoint(guest)
    env["PLT_INFO_FILE"] = guest + ".plt"
    env["BINRADAR_FORKSERVER_CHILD_TIMEOUT"] = str(test.get("fs_child_timeout", 4))
    if test.get("fs_iteration_timeout") is not None:
        env["BINRADAR_FORKSERVER_ITERATION_TIMEOUT"] = str(
            test["fs_iteration_timeout"])
    fs_binradar = test.get("fs_binradar", False)
    patch_r = patch_w = None
    if fs_binradar:
        env["BINRADAR_FORKSERVER_TIMEOUT_ABORT_COUNT"] = \
            str(test.get("fs_abort_count", 3))
        # binradar-mode marker for the tracer: patch shm (cur patch-id/
        # iter pair) + a patch-results pipe.  PATCH_CNT keeps the plan
        # alive across several iterations.
        patch_shm_key = random.getrandbits(30) | (1 << 29)
        libc = ctypes.CDLL("libc.so.6", use_errno=True)
        IPC_CREAT = 0o1000
        shmid = libc.shmget(ctypes.c_int(patch_shm_key), ctypes.c_size_t(8),
                            ctypes.c_int(0o666 | IPC_CREAT))
        if shmid == -1:
            raise RuntimeError(
                f"shmget failed: {ctypes.geterrno()}")
        env["BINRADAR_PATCH_SHM_KEY"] = hex(patch_shm_key)
        env["BINRADAR_PATCH_CNT"] = str(test.get("fs_patch_cnt", 2))
        env["BINRADAR_EVIDENCE_FILE"] = os.path.join(
            run_dir, "binradar.br")
        patch_r, patch_w = os.pipe()
        env["BINRADAR_PATCH_FD_R"] = str(patch_r)
    ctrl_r = ctrl_w = stat_r = stat_w = None
    try:
        prepare_symbolic_env(env, run_dir)
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
            env=env,
            pass_fds=(ctrl_r, stat_w) + ((patch_r,) if patch_r is not None else ()),
            stdout=subprocess.DEVNULL, stderr=stderr_fh,
            start_new_session=True,
        )
        os.close(ctrl_r)
        os.close(stat_w)
        if patch_r is not None:
            os.close(patch_r)
            patch_r = None

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
        banner_value = struct.unpack("<I", banner)[0]
        if banner_value != HANDSHAKE_EXPECTED:
            raise RuntimeError(f"unexpected forkserver banner: {banner_value:#x}")
        os.write(ctrl_w, struct.pack("<I", HANDSHAKE_EXPECTED ^ 0xFFFFFFFF))
        ack = read_exact(stat_r, 4)
        if len(ack) != 4:
            proc.wait(timeout=10)
            raise RuntimeError("forkserver ack EOF")
        ack_value = struct.unpack("<I", ack)[0]
        if ack_value != HANDSHAKE_EXPECTED:
            raise RuntimeError(f"unexpected forkserver ack: {ack_value:#x}")
        if test.get("check_local_solver_mapping"):
            check_local_solver_mapping(proc.pid)

        # Iterate attempts until the tracer reports a terminal stop reason.
        # Non-binradar forkserver tests see stop=exhausted after the first
        # attempt, i.e. exactly one child as before.
        child_status = None
        expected_attempt = 1
        summaries = []
        for _ in range(test.get("fs_max_attempts", 40)):
            if fs_binradar and expected_attempt > 1:
                for patch_id in range(1, test.get("fs_patch_cnt", 2) + 1):
                    row = (f"[patch] [id {patch_id}] [br 0] "
                           f"[v {expected_attempt}]\n").encode()
                    os.write(patch_w, row)
            os.write(ctrl_w, struct.pack("<I", 0))  # was_killed
            summary = read_exact(stat_r, 20)
            if len(summary) != 20:
                break
            attempt, representative_runs, remaining, attempt_result, \
                stop_reason = struct.unpack("<IIIII", summary)
            summaries.append((attempt, representative_runs, remaining,
                              attempt_result, stop_reason))
            if attempt != expected_attempt or representative_runs == 0:
                raise RuntimeError(
                    f"invalid forkserver summary: attempt={attempt}, "
                    f"runs={representative_runs}")
            expected_attempt += 1
            if stop_reason != STOP_CONTINUE:
                break

        os.close(ctrl_w)
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, 9)
            proc.wait(timeout=5)
        stderr_fh.close()
        with open(stderr_path, "r", errors="replace") as f:
            stderr_text = f.read()
        evidence = None
        if test.get("compact_fault_reference") or \
                "fs_evidence_attempts" in test:
            evidence_path = env["BINRADAR_EVIDENCE_FILE"]
            if os.path.isfile(evidence_path):
                evidence = list(binradar_evidence.read_binradar(
                    evidence_path))
        return (proc.returncode, child_status, stderr_text, evidence,
                _summarize(summaries))
    finally:
        if ctrl_w is not None:
            try:
                os.close(ctrl_w)
            except OSError:
                pass
        if patch_w is not None:
            try:
                os.close(patch_w)
            except OSError:
                pass
        if patch_r is not None:
            try:
                os.close(patch_r)
            except OSError:
                pass
        cleanup_shm(env)


def run_test(test, guests_dir, workdir, qemu):
    guest = os.path.join(workdir, test.get("guest", test["name"]))
    if not os.path.isfile(guest):
        raise FileNotFoundError(f"guest binary missing: {guest} (run 'make guests')")
    if test.get("meta"):
        sym_names = {v for k, v in test["meta"].items()
                     if k in ("producer_pc", "last_writer", "access_pc")}
        test["_symbols"] = resolve_symbols(guest, sym_names)
    evidence = None
    summary = None
    # Compaction fixtures only need the committed baseline frame; draining the
    # whole mutation queue would cost minutes without adding evidence shape.
    run_spec = dict(test)
    if test.get("fs_compaction_only"):
        run_spec["fs_max_attempts"] = 1
    with tempfile.TemporaryDirectory(prefix="prov-probe-") as probe_dir:
        probe_file = os.path.join(probe_dir, "probe.sbsv")
        run_spec = dict(run_spec, probe_file=probe_file)
        if test["mode"] == "mem":
            result = run_memcheck(run_spec, guest, qemu, workdir)
            rc, stderr_text = result.returncode, result.stderr.decode(errors="replace")
            fs_status = None
        elif test["mode"] == "sym":
            result = run_symbolic(run_spec, guest, qemu, workdir)
            rc, stderr_text = result.returncode, result.stderr.decode(errors="replace")
            fs_status = None
        else:
            rc, fs_status, stderr_text, evidence, summary = run_forkserver(
                run_spec, guest, qemu, workdir)
        probe_text = ""
        if os.path.isfile(probe_file):
            with open(probe_file, encoding="utf-8") as probe:
                probe_text = probe.read()

    return (rc, fs_status, stderr_text, evidence, probe_text, summary)


def check(test, rc, fs_status, out, evidence=None, probe_text="",
          summary=None):
    problems = []
    if not rc_ok(rc, test.get("rc", (0,))):
        problems.append(f"rc={rc} not in {test.get('rc')}")
    meta = test.get("meta")
    if meta:
        symbols = test.get("_symbols")
        if symbols is None:
            problems.append("meta test without resolved symbols")
        else:
            for field, want in meta.items():
                if field in ("producer_pc", "last_writer", "access_pc"):
                    if want not in symbols:
                        problems.append(f"meta {field}: unknown symbol {want!r}")
                elif field not in ("producer_kind", "ea_reg"):
                    problems.append(f"meta: unknown field {field!r}")
    if test["mode"] == "fors":
        want_status = test.get("fs_status")
        if want_status is not None and fs_status != want_status:
            problems.append(f"child status {fs_status} != {want_status}")
        want_stop = test.get("fs_stop")
        if want_stop is not None:
            if summary is None:
                problems.append("missing forkserver summary")
            elif summary["stop_name"] != want_stop:
                problems.append(
                    f"forkserver stop {summary['stop_name']!r} != "
                    f"{want_stop!r}")
        want_attempts = test.get("fs_attempts")
        if want_attempts is not None:
            if summary is None or summary["attempts"] != want_attempts:
                problems.append(
                    f"forkserver attempts "
                    f"{summary['attempts'] if summary else None} != "
                    f"{want_attempts}")
        want_min_attempts = test.get("fs_min_attempts")
        if want_min_attempts is not None:
            if summary is None or summary["attempts"] < want_min_attempts:
                problems.append(
                    f"forkserver attempts "
                    f"{summary['attempts'] if summary else None} < "
                    f"{want_min_attempts}")
        want_last_result = test.get("fs_attempt_result")
        if want_last_result is not None:
            if summary is None or \
                    summary["attempt_result"] != want_last_result:
                problems.append(
                    f"forkserver attempt result "
                    f"{summary['attempt_result'] if summary else None} != "
                    f"{want_last_result}")
        want_discards = test.get("fs_min_discarded")
        if want_discards is not None:
            if summary is None or summary["discarded"] < want_discards:
                problems.append(
                    f"forkserver discarded "
                    f"{summary['discarded'] if summary else None} < "
                    f"{want_discards}")
        want_remaining = test.get("fs_remaining")
        if want_remaining is not None:
            if summary is None or summary["remaining"] != want_remaining:
                problems.append(
                    f"forkserver remaining "
                    f"{summary['remaining'] if summary else None} != "
                    f"{want_remaining}")
        want_committed = test.get("fs_committed")
        if want_committed is not None:
            if summary is None or summary["committed"] != want_committed:
                problems.append(
                    f"forkserver committed "
                    f"{summary['committed'] if summary else None} != "
                    f"{want_committed}")
        if test.get("fs_only_no_observation_discards"):
            if summary is None:
                problems.append("missing summary for discarded-attempt outcomes")
            elif (summary["attempts"] < 2 or
                  summary["attempts"] != summary["initial_remaining"] + 1 or
                  summary["committed"] != 1 or
                  summary["no_observation"] != summary["attempts"] - 1):
                problems.append(
                    "mutation queue did not finish with only "
                    "no-observation discards "
                    f"(attempts={summary['attempts']}, "
                    f"initial-remaining={summary['initial_remaining']}, "
                    f"committed={summary['committed']}, "
                    f"no-observation={summary['no_observation']})")
        want_evidence_attempts = test.get("fs_evidence_attempts")
        if want_evidence_attempts is not None:
            evidence_attempts = ([iteration.iteration for iteration in evidence]
                                 if evidence is not None else None)
            if evidence_attempts != list(want_evidence_attempts):
                problems.append(
                    f"BINRADAR evidence attempts {evidence_attempts} != "
                    f"{list(want_evidence_attempts)}")
        want_discard_rows = test.get("fs_discard_reason")
        if want_discard_rows is not None:
            marker = f"[binradar] [attempt-discarded] [iter "
            if marker not in out:
                problems.append("missing attempt-discarded row")
            elif f"[reason {want_discard_rows}]" not in out:
                problems.append(
                    f"missing attempt-discarded reason {want_discard_rows!r}")
        want_abort = test.get("fs_abort_count")
        # 0 disables the consecutive-bad-attempt limit, so no failure-limit
        # row is expected; only a positive bound must produce one.
        if want_abort:
            marker = (f"[forkserver] [failure-limit] "
                      f"[consecutive-bad {want_abort}]")
            if marker not in out:
                problems.append(f"missing failure-limit line {marker!r}")
            if "[forkserver] [child-timeout]" not in out:
                problems.append("missing forkserver child-timeout line")

    verdict, final_query, final_expr = parse_exit_line(out)
    want_verdict = test["verdict"]
    if want_verdict is not None and verdict != want_verdict:
        problems.append(f"exit verdict {verdict!r} != {want_verdict!r}")
    reason = parse_crash_reason(out)
    if test.get("reason") and reason is None:
        problems.append("missing [snapshot] [crash] reason")
    elif test.get("reason") and test["reason"] not in reason:
        problems.append(f"crash reason {reason!r} != {test['reason']!r}")

    reference_expectation = test.get("fault_reference")
    if reference_expectation is not None:
        references = parse_fault_references(out)
        crashes = parse_crash_fault_addresses(out)
        addresses = [reference["address"] for reference in references]
        if not references:
            problems.append("missing normalized version-2 fault-reference row")
        for reference in references:
            if reference["valid"] != reference_expectation["valid"]:
                problems.append(
                    f"fault reference validity {reference['valid']!r} != "
                    f"{reference_expectation['valid']!r}")
            if reference["source"] != reference_expectation["source"]:
                problems.append(
                    f"fault reference source {reference['source']!r} != "
                    f"{reference_expectation['source']!r}")
            if reference_expectation.get("nonzero") and reference["address"] == 0:
                problems.append("signal fault reference unexpectedly uses PC zero")
        if addresses != crashes:
            problems.append(
                "fault-reference addresses disagree with structured crash rows")
        # Cross-channel agreement alone accepts the same wrong exit PC in
        # every channel. Anchor the identity to the independent finding or
        # signal PC, for every real child rather than only the last row.
        finding_pcs = [finding_int(finding, "access_pc")
                       for finding in parse_findings(out)]
        if reference_expectation["source"] == "provenance-access":
            if not finding_pcs or addresses != finding_pcs:
                problems.append("fault reference does not identify provenance access PC")
        elif reference_expectation["source"] == "guest-signal":
            signal_pcs = [int(pc, 16) for pc in re.findall(
                r"^\[snapshot\] \[crash\].*\[guest_pc ([0-9a-fA-F]+)\]",
                out, re.MULTILINE)]
            if addresses != signal_pcs:
                problems.append("fault reference does not identify signal guest PC")
            if finding_pcs and addresses == finding_pcs:
                problems.append("signal fixture did not distinguish deferred access PC")
        rows = [line for line in out.splitlines() if line.startswith((
            "[snapshot] [fault-reference]", "[snapshot] [crash]"))]
        probe_rows = [line for line in probe_text.splitlines() if line.startswith((
            "[snapshot] [fault-reference]", "[snapshot] [crash]"))]
        if rows != probe_rows:
            problems.append("probe file does not match normalized log publication")
        if len(rows) != 2 * len(references) or any(
                not row.startswith("[snapshot] [fault-reference]" if i % 2 == 0
                                   else "[snapshot] [crash]")
                for i, row in enumerate(rows)):
            problems.append("fault reference was not published before each crash row")

    if test.get("compact_fault_reference"):
        references = parse_fault_references(out)
        compact_faults = [
            group.fault_addr
            for iteration in (evidence or [])
            for group in iteration.groups
            if group.outcome == "crash"
        ]
        if not compact_faults:
            problems.append("compact evidence has no crash fault group")
        elif not references or any(
                fault != references[-1]["address"] for fault in compact_faults):
            problems.append(
                "compact evidence fault address disagrees with fault-reference row")

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
    if test.get("no_consistency"):
        # A consistency-mismatch on a changed-byte syscall output means the
        # invalidation hook was missing and only the value check dropped the
        # tag — the test would pass for the wrong reason.
        if re.search(r"^\[prov\] \[consistency\]", out, re.MULTILINE):
            problems.append("consistency-mismatch log present: missing "
                            "syscall output invalidation hook")
    if want is None:
        if findings and not test.get("allow_findings"):
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

    if meta:
        symbols = test.get("_symbols")
        if symbols is not None:
            if finding_int(got, "kind") != meta["producer_kind"]:
                problems.append(
                    f"producer kind {finding_int(got, 'kind')} != "
                    f"{meta['producer_kind']}")
            for field in ("producer_pc", "last_writer", "access_pc"):
                want_addr = symbols[meta[field]]
                if finding_int(got, field) != want_addr:
                    problems.append(
                        f"finding {field} {finding_int(got, field):#x} != "
                        f"{meta[field]} {want_addr:#x}")
            if finding_int(got, "ea_reg") != meta["ea_reg"]:
                problems.append(
                    f"ea_reg {finding_int(got, 'ea_reg')} != {meta['ea_reg']}")

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
        if finding_int(got, "ea_reg") < 0:
            problems.append("tagged finding has no EA register")

    cursors = test.get("cursors")
    if cursors:
        for field in ("query_cursor", "expr_cursor"):
            if field not in got:
                problems.append(f"missing {field} in finding")
        if final_query is None:
            problems.append("missing final query cursor")
        elif "query_cursor" in got and cursors.get("query_after"):
            if final_query <= finding_int(got, "query_cursor"):
                problems.append(
                    "final query cursor did not advance past finding")
        if final_expr is None:
            problems.append("missing final expression cursor")
        elif "expr_cursor" in got and cursors.get("expr_after"):
            if final_expr <= finding_int(got, "expr_cursor"):
                problems.append(
                    "final expression cursor did not advance past finding")
    return problems


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("guests", help="guests source dir (unused, for CLI parity)")
    ap.add_argument("work", help="work dir with built guests + .plt files")
    ap.add_argument("qemu", help="tracer binary")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--test", default=None, help="run only this test name")
    args = ap.parse_args()

    if not os.path.isfile(args.qemu):
        sys.exit(f"tracer binary not found: {args.qemu}")

    failures = []
    ran = 0
    for spec in TESTS:
        if args.test and spec["name"] != args.test:
            continue
        ran += 1
        start = time.time()
        try:
            rc, fs_status, out, evidence, probe_text, summary = run_test(
                spec, args.guests, args.work, args.qemu)
        except Exception as e:  # noqa: BLE001 — per-test isolation
            failures.append(spec)
            print(f"FAIL {spec['name']}: {e}")
            continue
        problems = check(spec, rc, fs_status, out, evidence, probe_text,
                         summary)
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
