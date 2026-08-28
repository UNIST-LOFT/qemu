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
from collections import Counter
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
        # Deterministic exact-component rejection.  Do not rely on an
        # incidental graph becoming oversized as fact identity improves.
        env={"BINRADAR_OSPREY_MAX_EXACT_CLIQUE_VARS": "1"},
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
        # Exact canonical rows asserted against the checked-in dump
        # (t01_regions.expected): the fixture runs under three distinct
        # PIE load biases (default + two forced BINRADAR_MMAP_START
        # values) and every dump must be byte-identical to the expected
        # file.  The lifecycle rows are deterministic: two live
        # allocations at one site (1f8), successful same-base reuse
        # (2af), forced-move realloc 16 -> 1 MiB (2e5 -> 312), failed
        # realloc preserving the old identity (348, alloc 377 -1),
        # realloc(p,0) (3ad), zero-size non-NULL malloc(0) (3e8), and
        # a RET-imm callee whose following stack access proves the caller
        # activation survived.  The checked-in file owns exact row values;
        # the separate assertions below own cross-row invariants.
        # Structural assertions on the parsed dump (see check_dump).
        dump_assert={
            "global_rows": 1,          # one merged G instance
            "recurse_frames": 4,       # recurse(3) -> 4 live frames
            "same_site_alloc_min": 2,   # two allocations at one site
            "same_base_reuse": True,    # free + malloc at same base
            "realloc_moved": True,      # 16 -> 1 MiB at a distinct base
            "failed_realloc_preserved": True,  # old identity survives
            "zero_size_nonnull": True,  # malloc(0) instance present
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
    dict(
        name="t02_chunk_widths",
        mode="dump_compare",
        # Exercise the OSPREY consumer without provenance.  The shared
        # translator dispatch must not depend on memcheck being enabled.
        memcheck=0,
        qemu_args=["-cpu", "qemu64,+xsave,+xsaveopt,+mpx"],
        # This fixture validates the merged F01 dump, not the known-invalid
        # later inference stages.  Reject immediately after fact collection
        # so one extra producer cannot trigger unbounded legacy graph work.
        env={"BINRADAR_OSPREY_MAX_VARIABLES": "1"},
        dump_stem="t02_dump",
        expected="t02_chunk_widths.expected",
        rc=(2,),
        # Exact canonical rows asserted against the checked-in dump
        # (t02_chunk_widths.expected), byte-identical across three PIE
        # load biases.  The fixture forces selected integer, atomic, paired,
        # SIMD (including two-byte PINSRW), x87, descriptor, MXCSR, and
        # FXSAVE/FXRSTOR producers.
        # The explicit qemu64 feature set makes XSAVE/XSAVEOPT deterministic
        # without enabling unrelated SSE4 paths unsupported by the symbolic
        # engine.  MPX is advertised but remains disabled by guest state; its
        # labeled BNDMOV operations must therefore stay absent.
        dump_assert={
            "access_symbols_absent": [
                "t02_fault_store", "t02_fault_paired_store",
                "t02_bndmov_load", "t02_bndmov_store",
            ],
            "access_widths_allowed": [
                1, 2, 4, 6, 8, 10, 16, 24, 28, 64, 108, 128, 256,
            ],
            "access_widths_min": {
                1: 1,    # byte store
                2: 1,    # word store
                4: 3,    # dword store + lock xadd + lock cmpxchg
                8: 4,    # qword store, lock xadd/cmpxchg qword,
                         # cmpxchg8b, movsd, fstl
                10: 2,   # fstpt + fbstp
                16: 1,   # movaps 128-bit
                28: 1,   # fnstenv (64-bit operand)
                108: 1,  # fnsave (64-bit operand)
                6: 2,    # x87 control fields in FXSAVE/FXRSTOR
                256: 2,  # FXSAVE + FXRSTOR XMM state
            },
            "access_classes_min": {0: 1, 1: 1, 2: 1, 3: 1, 4: 1},
            "access_symbols_expected": {
                "t02_pinsrw_load": {
                    "class": 1, "is_store": 0, "size": 2,
                    "min_rows": 1, "max_rows": 1,
                },
                "t02_maskmov": {
                    "class": 1, "is_store": 1, "size": 1,
                    "min_rows": 4, "max_rows": 4,
                },
                "t02_deep_enter": {
                    "class": 0, "size": 8,
                    "direction_counts": {0: 30, 1: 32},
                    "min_rows": 62, "max_rows": 62,
                },
                "t02_fxsave": {
                    "class": 4,
                    "sizes": {6: 1, 8: 1, 10: 8, 16: 1, 256: 1},
                    "direction_counts": {1: 12},
                    "min_rows": 12, "max_rows": 12,
                },
                "t02_fxrstor": {
                    "class": 4,
                    "sizes": {4: 1, 6: 1, 10: 8, 16: 1, 256: 1},
                    "direction_counts": {0: 12},
                    "min_rows": 12, "max_rows": 12,
                },
                "t02_xsave": {
                    "class": 4,
                    "sizes": {6: 1, 8: 3, 10: 8, 16: 1, 256: 1},
                    "direction_counts": {0: 1, 1: 13},
                    "min_rows": 14, "max_rows": 14,
                },
                "t02_xsaveopt": {
                    "class": 4,
                    "sizes": {6: 1, 8: 3, 10: 8, 16: 1, 256: 1},
                    "direction_counts": {0: 1, 1: 13},
                    "min_rows": 14, "max_rows": 14,
                },
                "t02_xrstor": {
                    "class": 4,
                    "sizes": {4: 1, 6: 1, 10: 8, 16: 1, 24: 1,
                              256: 1},
                    "direction_counts": {0: 13},
                    "min_rows": 13, "max_rows": 13,
                },
            },
        },
        timeout=60,
    ),
    dict(
        name="t02_chunk_widths_combined",
        guest="t02_chunk_widths",
        mode="dump_compare",
        # The same exact F01 matrix must remain stable when provenance and
        # OSPREY consume the neutral events together.
        memcheck=1,
        qemu_args=["-cpu", "qemu64,+xsave,+xsaveopt,+mpx"],
        env={"BINRADAR_OSPREY_MAX_VARIABLES": "1"},
        dump_stem="t02_combined_dump",
        expected="t02_chunk_widths.expected",
        rc=(2,),
        dump_assert={
            "access_symbols_absent": [
                "t02_fault_store", "t02_fault_paired_store",
                "t02_bndmov_load", "t02_bndmov_store",
            ],
            "access_widths_allowed": [
                1, 2, 4, 6, 8, 10, 16, 24, 28, 64, 108, 128, 256,
            ],
            "access_widths_min": {
                1: 1, 2: 1, 4: 3, 6: 2, 8: 4, 10: 2, 16: 1,
                28: 1, 108: 1, 256: 2,
            },
            "access_classes_min": {0: 1, 1: 1, 2: 1, 3: 1, 4: 1},
            "access_symbols_expected": {
                "t02_pinsrw_load": {
                    "class": 1, "is_store": 0, "size": 2,
                    "min_rows": 1, "max_rows": 1,
                },
                "t02_maskmov": {
                    "class": 1, "is_store": 1, "size": 1,
                    "min_rows": 4, "max_rows": 4,
                },
                "t02_deep_enter": {
                    "class": 0, "size": 8,
                    "direction_counts": {0: 30, 1: 32},
                    "min_rows": 62, "max_rows": 62,
                },
                "t02_fxsave": {
                    "class": 4,
                    "sizes": {6: 1, 8: 1, 10: 8, 16: 1, 256: 1},
                    "direction_counts": {1: 12},
                    "min_rows": 12, "max_rows": 12,
                },
                "t02_fxrstor": {
                    "class": 4,
                    "sizes": {4: 1, 6: 1, 10: 8, 16: 1, 256: 1},
                    "direction_counts": {0: 12},
                    "min_rows": 12, "max_rows": 12,
                },
                "t02_xsave": {
                    "class": 4,
                    "sizes": {6: 1, 8: 3, 10: 8, 16: 1, 256: 1},
                    "direction_counts": {0: 1, 1: 13},
                    "min_rows": 14, "max_rows": 14,
                },
                "t02_xsaveopt": {
                    "class": 4,
                    "sizes": {6: 1, 8: 3, 10: 8, 16: 1, 256: 1},
                    "direction_counts": {0: 1, 1: 13},
                    "min_rows": 14, "max_rows": 14,
                },
                "t02_xrstor": {
                    "class": 4,
                    "sizes": {4: 1, 6: 1, 10: 8, 16: 1, 24: 1,
                              256: 1},
                    "direction_counts": {0: 13},
                    "min_rows": 13, "max_rows": 13,
                },
            },
        },
        timeout=60,
    ),
    dict(
        name="t04_mpx",
        mode="dump_compare",
        memcheck=0,
        qemu_args=["-cpu", "qemu64,+xsave,+xsaveopt,+mpx"],
        dump_stem="t04_mpx_dump",
        expected="t04_mpx.expected",
        rc=(2,),
        dump_assert={
            "access_widths_allowed": [1, 8, 16, 24, 64],
            "access_classes_min": {4: 1, 10: 1},
            "access_symbols_expected": {
                "t04_mpx_enable": {
                    "class": 4, "is_store": 0,
                    "sizes": {16: 1, 24: 1, 64: 1},
                    "direction_counts": {0: 3},
                    "min_rows": 3, "max_rows": 3,
                },
                "t04_bndmov_load": {
                    "class": 10, "is_store": 0, "size": 16,
                    "min_rows": 1, "max_rows": 1,
                },
                "t04_bndmov_store": {
                    "class": 10, "is_store": 1, "size": 16,
                    "min_rows": 1, "max_rows": 1,
                },
                "t04_bndstx": {
                    "class": 10,
                    "sizes": {8: 1, 24: 1},
                    "direction_counts": {0: 1, 1: 1},
                    "min_rows": 2, "max_rows": 2,
                },
                "t04_bndldx": {
                    "class": 10, "is_store": 0,
                    "sizes": {8: 1, 24: 1},
                    "min_rows": 2, "max_rows": 2,
                },
                "t04_bndmov_after_load": {
                    "class": 10, "is_store": 1, "size": 16,
                    "min_rows": 1, "max_rows": 1,
                },
            },
        },
        timeout=60,
    ),
    dict(
        name="t04_mpx_combined",
        guest="t04_mpx",
        mode="dump_compare",
        memcheck=1,
        qemu_args=["-cpu", "qemu64,+xsave,+xsaveopt,+mpx"],
        dump_stem="t04_mpx_combined_dump",
        expected="t04_mpx.expected",
        rc=(2,),
        dump_assert={
            "access_widths_allowed": [1, 8, 16, 24, 64],
            "access_classes_min": {4: 1, 10: 1},
            "access_symbols_expected": {
                "t04_mpx_enable": {
                    "class": 4, "is_store": 0,
                    "sizes": {16: 1, 24: 1, 64: 1},
                    "direction_counts": {0: 3},
                    "min_rows": 3, "max_rows": 3,
                },
                "t04_bndmov_load": {
                    "class": 10, "is_store": 0, "size": 16,
                    "min_rows": 1, "max_rows": 1,
                },
                "t04_bndmov_store": {
                    "class": 10, "is_store": 1, "size": 16,
                    "min_rows": 1, "max_rows": 1,
                },
                "t04_bndstx": {
                    "class": 10,
                    "sizes": {8: 1, 24: 1},
                    "direction_counts": {0: 1, 1: 1},
                    "min_rows": 2, "max_rows": 2,
                },
                "t04_bndldx": {
                    "class": 10, "is_store": 0,
                    "sizes": {8: 1, 24: 1},
                    "min_rows": 2, "max_rows": 2,
                },
                "t04_bndmov_after_load": {
                    "class": 10, "is_store": 1, "size": 16,
                    "min_rows": 1, "max_rows": 1,
                },
            },
        },
        timeout=60,
    ),
    dict(
        name="t05_enter_fault",
        mode="dump_compare",
        memcheck=0,
        dump_stem="t05_enter_fault_dump",
        expected=None,
        # This rejection fixture pivots to an mmap-backed stack.  The
        # translator's call/RSP identity is not a cross-bias-stable contract
        # for that pivot, so compare one deterministic run only; t02 owns
        # successful cross-bias stack coverage.
        biases=[None],
        compare_biases=False,
        rc=(2,),
        dump_assert={
            "access_symbols_absent": ["t05_enter_fault"],
        },
        timeout=60,
    ),
    dict(
        name="t05_enter_fault_combined",
        guest="t05_enter_fault",
        mode="dump_compare",
        memcheck=1,
        dump_stem="t05_enter_fault_combined_dump",
        expected=None,
        # Same custom-stack limitation as the OSPREY-only rejection case.
        biases=[None],
        compare_biases=False,
        rc=(2,),
        dump_assert={
            "access_symbols_absent": ["t05_enter_fault"],
        },
        timeout=60,
    ),
    dict(
        name="t06_control_reject",
        mode="binradar",
        memcheck=0,
        rc=(2,),
        expect_rows=[
            ("reject", "[stage merge] [reason unsupported guest execution]"),
        ],
        expect_inferred=0,
        expect_inferred_max=0,
        expect_queue_min=1,
        timeout=60,
    ),
    dict(
        name="t07_legacy_width_reject",
        mode="binradar",
        memcheck=0,
        rc=(2,),
        expect_rows=[
            ("reject", "[stage merge] [reason unsupported guest execution]"),
        ],
        expect_inferred=0,
        expect_inferred_max=0,
        expect_queue_min=1,
        timeout=60,
    ),
    dict(
        name="t08_bound_reject",
        mode="binradar",
        memcheck=0,
        rc=(2,),
        expect_rows=[
            ("reject", "[stage merge] [reason unsupported guest execution]"),
        ],
        expect_inferred=0,
        expect_inferred_max=0,
        expect_queue_min=1,
        timeout=60,
    ),
    dict(
        name="t09_address_origins",
        mode="dump_compare",
        # Exercise the OSPREY address-origin/F02 channel without
        # provenance; the shared translator dispatch must not depend on
        # memcheck being enabled.
        memcheck=0,
        # This fixture validates the merged F01/F02 dump, not the
        # known-invalid later inference stages.  Reject immediately after
        # fact collection.
        env={"BINRADAR_OSPREY_MAX_VARIABLES": "1"},
        dump_stem="t09_dump",
        expected="t09_address_origins.expected",
        rc=(2,),
        # Exact canonical rows asserted against the checked-in dump
        # (t09_address_origins.expected), byte-identical across three PIE
        # load biases.  Every positive access label owns exactly one base
        # row with the expected normalized producer PC; every negative
        # label is absent from the base rows.
        dump_assert={
            "access_symbols_absent": [
                "t09_no_base_segment", "t09_fault_access",
            ],
            "access_symbols_expected": {
                "t09_no_base_scaled": {"min_rows": 1, "max_rows": 1},
                "t09_no_base_indexed_lea": {"min_rows": 1, "max_rows": 1},
                "t09_no_base_stale": {"min_rows": 1, "max_rows": 1},
                "t09_no_base_simd": {"min_rows": 1, "max_rows": 1},
            },
            "base_symbols_expected": {
                "t09_access_global_rip": {
                    "producer": "t09_prod_global_rip", "kind": 0,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_stack_mov": {
                    "producer": "t09_prod_stack_mov", "kind": 2,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_mov": {
                    "producer": "t09_prod_heap_mov", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_self_mov": {
                    "producer": "t09_prod_heap_self_mov", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_self_lea": {
                    "producer": "t09_prod_heap_self_lea", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_reload": {
                    "producer": "t09_prod_heap_reload", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_lea": {
                    "producer": "t09_prod_heap_lea", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_add_imm": {
                    "producer": "t09_prod_heap_add_imm", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_sub_imm": {
                    "producer": "t09_prod_heap_sub_imm", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_add_reg": {
                    "producer": "t09_prod_heap_add_reg", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_xchg": {
                    "producer": "t09_prod_heap_xchg", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_base_index": {
                    "producer": "t09_prod_heap_index_base", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_index_only": {
                    "producer": "t09_prod_heap_index_base", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_self_load": {
                    "producer": "t09_prod_self_base", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
            },
            "base_symbols_absent": [
                "t09_no_base_scaled", "t09_no_base_indexed_lea",
                "t09_no_base_segment", "t09_no_base_stale",
                "t09_no_base_simd", "t09_fault_access",
            ],
            # Stage 2.4: live heap-pointer stores are valid F04
            # observations; exact rows live in the checked-in dump
            # (first malloc site 0x297).
            "points_expected": [
                ("g_heap_ptr", "alloc_297"),
                ("g_pointer_slot", "alloc_297"),
            ],
        },
        timeout=60,
    ),
    dict(
        name="t09_address_origins_combined",
        guest="t09_address_origins",
        mode="dump_compare",
        # The same exact F01/F02 dump must remain stable when provenance
        # and OSPREY consume the neutral events together.  Provenance
        # legitimately reports the deliberate stale fixture
        # (t09_no_base_stale) as heap-use-after-free.  The shared F01/F02
        # dump and tracer outcome must nevertheless be deterministic
        # across the same three verified PIE biases.
        memcheck=1,
        env={"BINRADAR_OSPREY_MAX_VARIABLES": "1"},
        dump_stem="t09_combined_dump",
        expected="t09_address_origins.expected",
        rc=(2,),
        dump_assert={
            "access_symbols_absent": [
                "t09_no_base_segment", "t09_fault_access",
            ],
            "access_symbols_expected": {
                "t09_no_base_scaled": {"min_rows": 1, "max_rows": 1},
                "t09_no_base_indexed_lea": {"min_rows": 1, "max_rows": 1},
                "t09_no_base_stale": {"min_rows": 1, "max_rows": 1},
                "t09_no_base_simd": {"min_rows": 1, "max_rows": 1},
            },
            "base_symbols_expected": {
                "t09_access_global_rip": {
                    "producer": "t09_prod_global_rip", "kind": 0,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_stack_mov": {
                    "producer": "t09_prod_stack_mov", "kind": 2,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_mov": {
                    "producer": "t09_prod_heap_mov", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_self_mov": {
                    "producer": "t09_prod_heap_self_mov", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_self_lea": {
                    "producer": "t09_prod_heap_self_lea", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_reload": {
                    "producer": "t09_prod_heap_reload", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_lea": {
                    "producer": "t09_prod_heap_lea", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_add_imm": {
                    "producer": "t09_prod_heap_add_imm", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_sub_imm": {
                    "producer": "t09_prod_heap_sub_imm", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_add_reg": {
                    "producer": "t09_prod_heap_add_reg", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_xchg": {
                    "producer": "t09_prod_heap_xchg", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_base_index": {
                    "producer": "t09_prod_heap_index_base", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_heap_index_only": {
                    "producer": "t09_prod_heap_index_base", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
                "t09_access_self_load": {
                    "producer": "t09_prod_self_base", "kind": 1,
                    "min_rows": 1, "max_rows": 1,
                },
            },
            "base_symbols_absent": [
                "t09_no_base_scaled", "t09_no_base_indexed_lea",
                "t09_no_base_segment", "t09_no_base_stale",
                "t09_no_base_simd", "t09_fault_access",
            ],
            # Stage 2.4: live heap-pointer stores are valid F04
            # observations; exact rows live in the checked-in dump
            # (first malloc site 0x297).
            "points_expected": [
                ("g_heap_ptr", "alloc_297"),
                ("g_pointer_slot", "alloc_297"),
            ],
        },
        timeout=60,
    ),
    dict(
        name="t10_value_origins",
        mode="dump_compare",
        # Exercise the OSPREY VALUE-origin/F03/F04 channel without
        # provenance; the shared translator dispatch must not depend on
        # memcheck being enabled.
        memcheck=0,
        env={"BINRADAR_OSPREY_MAX_VARIABLES": "1"},
        dump_stem="t10_dump",
        expected="t10_value_origins.expected",
        rc=(2,),
        # Exact canonical rows asserted against the checked-in dump,
        # byte-identical across three PIE load biases.
        dump_assert={
            "copy_chunks_expected": [
                ("g_src_qword", "g_dst_qword", 8),
                ("alloc_31d", "g_dst_qword", 1),
                ("alloc_31d", "g_dst_qword", 2),
                ("alloc_31d", "g_dst_qword", 4),
                ("alloc_31d", "g_dst_qword", 8),
            ],
            "points_expected": [
                ("g_pointer_slot_1", "alloc_31d"),
                ("g_pointer_slot_2", "alloc_31d"),
            ],
            "points_absent": [
                ("g_pointer_slot_1", "alloc_4bf"),
            ],
        },
        timeout=60,
    ),
    dict(
        name="t10_value_origins_combined",
        guest="t10_value_origins",
        mode="dump_compare",
        # The same exact F03/F04 dump must remain stable when
        # provenance and OSPREY consume the neutral events together.
        memcheck=1,
        env={"BINRADAR_OSPREY_MAX_VARIABLES": "1"},
        dump_stem="t10_combined_dump",
        expected="t10_value_origins.expected",
        rc=(2,),
        dump_assert={
            "copy_chunks_expected": [
                ("g_src_qword", "g_dst_qword", 8),
                ("alloc_31d", "g_dst_qword", 1),
                ("alloc_31d", "g_dst_qword", 2),
                ("alloc_31d", "g_dst_qword", 4),
                ("alloc_31d", "g_dst_qword", 8),
            ],
            "points_expected": [
                ("g_pointer_slot_1", "alloc_31d"),
                ("g_pointer_slot_2", "alloc_31d"),
            ],
        },
        timeout=60,
    ),
    dict(
        name="t11_modeled_copies",
        mode="dump_compare",
        # Exercise the PLT-model copy paths (memcpy/memmove/strcpy/
        # strncpy/memset) without provenance.
        memcheck=0,
        env={"BINRADAR_OSPREY_MAX_VARIABLES": "1"},
        dump_stem="t11_dump",
        expected="t11_modeled_copies.expected",
        rc=(2,),
        dump_assert={
            "copy_chunks_expected": [
                ("g_src", "g_dst", 13),
                ("g_lit_abc", "g_str_dst", 4),
                ("g_pointer_slot", "g_pointer_slot2", 8),
            ],
            "copy_chunks_absent": [
                ("g_str_dst", "g_str_dst", 8),
            ],
            "points_expected": [
                ("g_pointer_slot2", "alloc_36d"),
            ],
        },
        timeout=60,
    ),
    dict(
        name="t11_modeled_copies_combined",
        guest="t11_modeled_copies",
        mode="dump_compare",
        # The same exact modeled-copy dump must remain stable when
        # provenance and OSPREY consume the neutral events together.
        memcheck=1,
        env={"BINRADAR_OSPREY_MAX_VARIABLES": "1"},
        dump_stem="t11_combined_dump",
        expected="t11_modeled_copies.expected",
        rc=(2,),
        dump_assert={
            "copy_chunks_expected": [
                ("g_src", "g_dst", 13),
                ("g_lit_abc", "g_str_dst", 4),
                ("g_pointer_slot", "g_pointer_slot2", 8),
            ],
            "points_expected": [
                ("g_pointer_slot2", "alloc_36d"),
            ],
        },
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


def resolve_symbol(guest, symbol):
    """Return a linked symbol value; PIE values are image-relative."""
    nm = subprocess.run(["nm", guest], capture_output=True, text=True)
    for line in nm.stdout.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[2] == symbol:
            return int(parts[0], 16)
    raise RuntimeError(f"no {symbol!r} symbol in {guest}")


def resolve_access_symbol(guest, symbol):
    """Map a linked text symbol to the tracer's image-relative PC."""
    text_base = None
    readelf = subprocess.run(["readelf", "-lW", guest],
                             capture_output=True, text=True)
    for line in readelf.stdout.splitlines():
        parts = line.split()
        if (len(parts) >= 7 and parts[0] == "LOAD" and
                "E" in parts[6:-1]):
            text_base = int(parts[2], 16)
            break
    if text_base is None:
        raise RuntimeError(f"no executable LOAD segment in {guest}")
    return resolve_symbol(guest, symbol) - text_base


def resolve_dump_symbol(guest, symbol):
    """Map a global data symbol to its canonical (kind, site, offset)
    triple for copy/points assertions: main-image writable globals are
    region G with image-relative offsets.  Symbols named `alloc_<site>`
    or `stack_<site>` resolve to synthetic site anchors for heap and
    stack targets (kind 1 / kind 2)."""
    if symbol.startswith("alloc_"):
        site = int(symbol[len("alloc_"):], 16)
        return (1, site, 0)
    if symbol.startswith("stack_"):
        site = int(symbol[len("stack_"):], 16)
        return (2, site, 0)
    # Ordinary data symbols: the tracer anchors the merged global region
    # at the main image's executable LOAD base (symbolic_start_code),
    # so offsets are symbol_value - text_base.
    text_base = None
    readelf = subprocess.run(["readelf", "-lW", guest],
                             capture_output=True, text=True)
    for line in readelf.stdout.splitlines():
        parts = line.split()
        if (len(parts) >= 7 and parts[0] == "LOAD" and
                "E" in parts[6:-1]):
            text_base = int(parts[2], 16)
            break
    if text_base is None:
        raise RuntimeError(f"no executable LOAD segment in {guest}")
    return (0, 0, resolve_symbol(guest, symbol) - text_base)


def resolve_entrypoint(guest):
    """main() symbol value from nm; elfload adds the PIE load bias."""
    return hex(resolve_symbol(guest, "main"))


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
    env["BINRADAR_MEMCHECK_ENABLE"] = str(test.get("memcheck", 1))
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
            [qemu, *test.get("qemu_args", []), "-symbolic", guest],
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
    """Stage-1 canonical-dump gate: run the guest under three distinct
    PIE load biases (default + two forced BINRADAR_MMAP_START values),
    require byte-identical dumps (ASLR invariance), then compare every
    dump against the checked-in exact canonical rows
    (t01_regions.expected).  Returns (tracer_rc, stderr_text)."""
    guest = os.path.join(workdir, test.get("guest", test["name"]))
    if not os.path.isfile(guest):
        return (None, f"guest binary missing: {guest} (run 'make guests')")
    if not os.path.isfile(guest + ".plt"):
        return (None, f"plt file missing: {guest}.plt (run 'make plts')")
    expected = None
    expected_name = test.get("expected", "t01_regions.expected")
    if expected_name is not None:
        expected_path = os.path.join(os.path.dirname(__file__), expected_name)
        if not os.path.isfile(expected_path):
            return (None, f"expected dump missing: {expected_path}")
        with open(expected_path, "r", errors="replace") as f:
            expected = f.read()
    biases = test.get("biases", [None, "0x4100000000", "0x4200000000"])
    dump_stem = test.get("dump_stem", "t01_dump")
    dumps = []
    outs = []
    rcs = []
    observed_biases = []
    for i, bias in enumerate(biases):
        dump_path = os.path.join(workdir, f"{dump_stem}_{i}.txt")
        try:
            os.unlink(dump_path)
        except OSError:
            pass
        spec = dict(test)
        spec["env"] = dict(test.get("env", {}))
        spec["env"]["BINRADAR_OSPREY_DUMP_FILE"] = dump_path
        if bias is not None:
            spec["env"]["BINRADAR_MMAP_START"] = bias
        rc, out = run_binradar(spec, guest, qemu, solver, workdir)
        rcs.append(rc)
        outs.append(out)
        matches = re.findall(
            r"\[snapshot\] \[entrypoint\].*\[bias ([0-9a-fA-F]+)\]",
            out,
        )
        if len(matches) != 1:
            return (None, out +
                    f"\nexpected one main-image bias row, got {matches}")
        observed_biases.append(int(matches[0], 16))
        if not os.path.isfile(dump_path):
            return (None, out + f"\nmissing dump file: {dump_path}")
        with open(dump_path, "r", errors="replace") as f:
            dumps.append(f.read())
    if test.get("compare_biases", True):
        for i in range(1, len(dumps)):
            if dumps[i] != dumps[0]:
                return (None, outs[0] +
                        f"\nDUMP MISMATCH between bias runs {0} and {i}")
        if len(set(observed_biases)) != len(observed_biases):
            return (None, outs[0] +
                    f"\nPIE load biases were not distinct: {observed_biases}")
    if expected is not None and dumps[0] != expected:
        return (None, outs[0] + "\nDUMP MISMATCH vs checked-in expected")
    problems = check_dump(test, dumps[0], guest)
    if problems:
        return (None, outs[0] + "\n" + "\n".join(problems))
    if len(set(rcs)) != 1:
        return (rcs[-1], outs[0] +
                f"\ntracer return codes differ: {rcs}")
    return (rcs[-1], outs[0])


def check_dump(test, dump, guest):
    """Structural assertions on the canonical dump."""
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

    if want.get("realloc_moved"):
        # forced-move realloc: the 1 MiB result instance (extent
        # 100000) must be at a base distinct from its 16-byte source
        # (the source's raw class appears once, the result's once).
        from collections import Counter
        raw_classes = Counter(r[4] for r in heap_rows)
        big = [r for r in heap_rows if r[5] == "100000"]
        moved = any(raw_classes[r[4]] == 1 for r in big)
        if not moved:
            problems.append("no forced-move realloc at distinct base")

    if want.get("failed_realloc_preserved"):
        # failed realloc: the 8-byte instance at site 348 survives with
        # its original extent; the failed alloc row (size -1) exists
        allocs = [ln.split() for ln in dump.splitlines()
                  if ln.startswith("alloc ")]
        failed = any(a[2] == "-1" for a in allocs)
        survivor = any(
            r[2] == "348" and r[5] == "8" for r in heap_rows)
        if not (failed and survivor):
            problems.append("failed realloc did not preserve old identity")

    if want.get("zero_size_nonnull"):
        # malloc(0): a heap instance with extent 0 (zero-size success)
        zero = any(r[5] == "0" for r in heap_rows)
        if not zero:
            problems.append("no zero-size non-NULL instance observed")

    if "access_widths_allowed" in want or "access_widths_min" in want:
        # F01 access facts: every recorded width must be one of the
        # canonical opcode widths (a width like 3 or 5 means a chunk was
        # mis-sized), and each width exercised by this fixture must appear.
        # access <pc> <is_store> <kind> <site> <offset> <size> <support>
        widths = [int(a[6]) for a in
                  (ln.split() for ln in dump.splitlines()
                   if ln.startswith("access "))]
        allowed = set(want.get("access_widths_allowed", []))
        for w in widths:
            if allowed and w not in allowed:
                problems.append(f"access fact width {w} not in "
                                f"{sorted(allowed)}")
        from collections import Counter
        got = Counter(widths)
        for w, n in want.get("access_widths_min", {}).items():
            if got[w] < n:
                problems.append(
                    f"access facts of width {w}: {got[w]} < {n}")
        for w in want.get("access_widths_absent", []):
            if got[w] != 0:
                problems.append(
                    f"forbidden access facts of width {w}: {got[w]}")

    access_rows = [ln.split() for ln in dump.splitlines()
                   if ln.startswith("access ")]
    if "access_classes_min" in want:
        classes = Counter(int(row[8]) if len(row) > 8 else 0
                          for row in access_rows)
        for cls, n in want["access_classes_min"].items():
            if classes[cls] < n:
                problems.append(
                    f"access facts of class {cls}: {classes[cls]} < {n}")

    access_pcs = {
        int(fields[1], 16)
        for fields in (ln.split() for ln in dump.splitlines())
        if fields and fields[0] == "access"
    }
    for symbol in want.get("access_symbols_absent", []):
        pc = resolve_access_symbol(guest, symbol)
        if pc in access_pcs:
            problems.append(
                f"access symbol {symbol} unexpectedly recorded at {pc:x}")
    for symbol, policy in want.get("access_symbols_expected", {}).items():
        pc = resolve_access_symbol(guest, symbol)
        rows = [row for row in access_rows if int(row[1], 16) == pc]
        if len(rows) < policy.get("min_rows", 1):
            problems.append(
                f"access symbol {symbol} rows {len(rows)} < "
                f"{policy.get('min_rows', 1)}")
        for row in rows:
            row_class = int(row[8]) if len(row) > 8 else 0
            if "class" in policy and row_class != policy["class"]:
                problems.append(
                    f"access symbol {symbol} class {row_class} != "
                    f"{policy['class']}")
            if "is_store" in policy and int(row[2]) != policy["is_store"]:
                problems.append(
                    f"access symbol {symbol} direction {row[2]} != "
                    f"{policy['is_store']}")
            if "directions" in policy and int(row[2]) not in policy["directions"]:
                problems.append(
                    f"access symbol {symbol} direction {row[2]} not in "
                    f"{sorted(policy['directions'])}")
            if "size" in policy and int(row[6]) != policy["size"]:
                problems.append(
                    f"access symbol {symbol} size {row[6]} != "
                    f"{policy['size']}")
        if "max_rows" in policy and len(rows) > policy["max_rows"]:
            problems.append(
                f"access symbol {symbol} rows {len(rows)} > "
                f"{policy['max_rows']}")
        if "direction_counts" in policy:
            directions = Counter(int(row[2]) for row in rows)
            expected = Counter(policy["direction_counts"])
            if directions != expected:
                problems.append(
                    f"access symbol {symbol} direction counts "
                    f"{dict(directions)} != {dict(expected)}")
        if "sizes" in policy:
            sizes = Counter(int(row[6]) for row in rows)
            expected = Counter(policy["sizes"])
            if sizes != expected:
                problems.append(
                    f"access symbol {symbol} sizes {dict(sizes)} != "
                    f"{dict(expected)}")

    # Stage 2.3 base rows: strict 13-token format
    # `base <access-pc-hex> <chunk-kind> <chunk-site-hex>
    # <chunk-offset-hex> <chunk-size-dec> <base-kind> <base-site-hex>
    # <base-offset-hex> <prov-id> <generation> <producer-pc-hex>
    # <support>`; every token must parse, and the access/producer PCs
    # must resolve exactly to the labeled symbols.
    base_rows = [ln.split() for ln in dump.splitlines()
                 if ln.startswith("base ")]
    for row in base_rows:
        if len(row) != 13:
            problems.append(f"malformed base row: {' '.join(row)}")
            continue
        try:
            int(row[1], 16)   # access pc
            int(row[2])       # chunk kind
            int(row[3], 16)   # chunk site
            int(row[4], 16)   # chunk offset
            int(row[5])       # chunk size
            int(row[6])       # base kind
            int(row[7], 16)   # base site
            int(row[8], 16)   # base offset
            int(row[9])       # prov id
            int(row[10])      # generation
            int(row[11], 16)  # producer pc
            int(row[12])      # support
        except ValueError:
            problems.append(f"malformed base row: {' '.join(row)}")
    base_by_access_pc = {}
    for row in base_rows:
        base_by_access_pc.setdefault(int(row[1], 16), []).append(row)

    for symbol, policy in want.get("base_symbols_expected", {}).items():
        access_pc = resolve_access_symbol(guest, symbol)
        producer_pc = resolve_access_symbol(guest, policy["producer"])
        rows = base_by_access_pc.get(access_pc, [])
        if len(rows) < policy.get("min_rows", 1):
            problems.append(
                f"base symbol {symbol} rows {len(rows)} < "
                f"{policy.get('min_rows', 1)}")
        for row in rows:
            if int(row[2]) != policy["kind"] or \
                    int(row[6]) != policy["kind"]:
                problems.append(
                    f"base symbol {symbol} kinds "
                    f"{row[2]}/{row[6]} != {policy['kind']}")
            if int(row[11], 16) != producer_pc:
                problems.append(
                    f"base symbol {symbol} producer {row[11]} != "
                    f"{producer_pc:x} ({policy['producer']})")
        if "max_rows" in policy and len(rows) > policy["max_rows"]:
            problems.append(
                f"base symbol {symbol} rows {len(rows)} > "
                f"{policy['max_rows']}")

    for symbol in want.get("base_symbols_absent", []):
        access_pc = resolve_access_symbol(guest, symbol)
        if access_pc in base_by_access_pc:
            problems.append(
                f"base symbol {symbol} unexpectedly has a base row")

    if want.get("no_copy_points"):
        if any(ln.startswith("copy ") or ln.startswith("points ")
               for ln in dump.splitlines()):
            problems.append("unexpected copy/points rows in dump")

    # Stage 2.4 copy rows: strict 10-token format
    # `copy <src-kind> <src-site-hex> <src-offset-hex> <src-size-dec>
    # <dst-kind> <dst-site-hex> <dst-offset-hex> <dst-size-dec>
    # <support>`.
    copy_rows = [ln.split() for ln in dump.splitlines()
                 if ln.startswith("copy ")]
    for row in copy_rows:
        if len(row) != 10:
            problems.append(f"malformed copy row: {' '.join(row)}")
            continue
        try:
            int(row[1])       # src kind
            int(row[2], 16)   # src site
            int(row[3], 16)   # src offset
            int(row[4])       # src size
            int(row[5])       # dst kind
            int(row[6], 16)   # dst site
            int(row[7], 16)   # dst offset
            int(row[8])       # dst size
            int(row[9])       # support
        except ValueError:
            problems.append(f"malformed copy row: {' '.join(row)}")

    # Stage 2.4 points rows: strict 10-token format
    # `points <cell-kind> <cell-site-hex> <cell-offset-hex>
    # <cell-size-dec> <target-kind> <target-site-hex>
    # <target-offset-hex> <support> <weak-numeric>`.
    points_rows = [ln.split() for ln in dump.splitlines()
                   if ln.startswith("points ")]
    for row in points_rows:
        if len(row) != 10:
            problems.append(f"malformed points row: {' '.join(row)}")
            continue
        try:
            int(row[1])       # cell kind
            int(row[2], 16)   # cell site
            int(row[3], 16)   # cell offset
            int(row[4])       # cell size
            int(row[5])       # target kind
            int(row[6], 16)   # target site
            int(row[7], 16)   # target offset
            int(row[8])       # support
            int(row[9])       # weak-numeric
        except ValueError:
            problems.append(f"malformed points row: {' '.join(row)}")
        if int(row[9]) != 0:
            problems.append(
                f"points row has nonzero weak-numeric evidence: "
                f"{' '.join(row)}")

    # Exact copy-row assertions: `copy_chunks_expected` maps a
    # `(src_symbol, dst_symbol, width)` triple to a count; each member
    # resolves through global data symbols and normalized allocation/
    # stack sites.  Counts must be exact, not minimum-only.
    def row_matches_fields(row, symbol_map, kind_idx, site_idx,
                           offset_idx, size_idx):
        kind = int(row[kind_idx])
        site = int(row[site_idx], 16)
        offset = int(row[offset_idx], 16)
        size = int(row[size_idx])
        for label, (k, s, off, w) in symbol_map.items():
            if k == kind and s == site and off == offset and w == size:
                return label
        return None

    copy_symbols = {}
    for (src_sym, dst_sym, width) in want.get("copy_chunks_expected", []):
        copy_symbols.setdefault((src_sym, dst_sym, width), 0)
    for row in copy_rows:
        for (src_sym, dst_sym, width) in list(copy_symbols.keys()):
            src_info = resolve_dump_symbol(guest, src_sym)
            dst_info = resolve_dump_symbol(guest, dst_sym)
            if src_info is None or dst_info is None:
                continue
            if (int(row[1]) == src_info[0] and
                    int(row[2], 16) == src_info[1] and
                    int(row[3], 16) == src_info[2] and
                    int(row[4]) == width and
                    int(row[5]) == dst_info[0] and
                    int(row[6], 16) == dst_info[1] and
                    int(row[7], 16) == dst_info[2] and
                    int(row[8]) == width):
                copy_symbols[(src_sym, dst_sym, width)] += 1
    for (src_sym, dst_sym, width), count in copy_symbols.items():
        if count < 1:
            problems.append(
                f"copy chunk {src_sym} -> {dst_sym} width {width} "
                f"missing (got {count})")
    for (src_sym, dst_sym, width) in want.get("copy_chunks_absent", []):
        present = False
        for row in copy_rows:
            src_info = resolve_dump_symbol(guest, src_sym)
            dst_info = resolve_dump_symbol(guest, dst_sym)
            if src_info is None or dst_info is None:
                continue
            if (int(row[1]) == src_info[0] and
                    int(row[2], 16) == src_info[1] and
                    int(row[3], 16) == src_info[2] and
                    int(row[4]) == width and
                    int(row[5]) == dst_info[0] and
                    int(row[6], 16) == dst_info[1] and
                    int(row[7], 16) == dst_info[2] and
                    int(row[8]) == width):
                present = True
                break
        if present:
            problems.append(
                f"copy chunk {src_sym} -> {dst_sym} width {width} "
                "unexpectedly present")

    # Exact points-row assertions: `points_expected` maps a
    # `(cell_symbol, target_symbol)` pair to a count; `points_absent`
    # lists pairs that must not appear.  Target symbols resolve through
    # the normalized allocation/global/stack sites.
    points_seen = {}
    for (cell_sym, target_sym) in want.get("points_expected", []):
        points_seen.setdefault((cell_sym, target_sym), 0)
    for row in points_rows:
        for (cell_sym, target_sym) in list(points_seen.keys()):
            cell_info = resolve_dump_symbol(guest, cell_sym)
            tgt_info = resolve_dump_symbol(guest, target_sym)
            if cell_info is None or tgt_info is None:
                continue
            if (int(row[1]) == cell_info[0] and
                    int(row[2], 16) == cell_info[1] and
                    int(row[3], 16) == cell_info[2] and
                    int(row[4]) == 8 and
                    int(row[5]) == tgt_info[0] and
                    int(row[6], 16) == tgt_info[1] and
                    int(row[7], 16) == tgt_info[2]):
                points_seen[(cell_sym, target_sym)] += 1
    for (cell_sym, target_sym), count in points_seen.items():
        if count < 1:
            problems.append(
                f"points {cell_sym} -> {target_sym} missing (got {count})")
    for (cell_sym, target_sym) in want.get("points_absent", []):
        present = False
        for row in points_rows:
            cell_info = resolve_dump_symbol(guest, cell_sym)
            tgt_info = resolve_dump_symbol(guest, target_sym)
            if cell_info is None or tgt_info is None:
                continue
            if (int(row[1]) == cell_info[0] and
                    int(row[2], 16) == cell_info[1] and
                    int(row[3], 16) == cell_info[2] and
                    int(row[4]) == 8 and
                    int(row[5]) == tgt_info[0] and
                    int(row[6], 16) == tgt_info[1] and
                    int(row[7], 16) == tgt_info[2]):
                present = True
                break
        if present:
            problems.append(
                f"points {cell_sym} -> {target_sym} unexpectedly present")
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
