#!/usr/bin/env python3
"""Sanity-check the currently enumerated semantic memory producers.

This is deliberately a source check, not an OSPREY collection path or a
complete producer inventory.  It recognizes direct qemu loads/stores, TCG
atomic operations, and a bounded helper-name set, then requires a nearby
class-carrying semantic event.  It does not parse C control flow, function
pointer helpers, or unlisted helper bodies; the Stage 2.2 audit documents
those remaining coverage gaps.
"""

from pathlib import Path
import re
import sys


TRANSLATE = Path(__file__).resolve().parents[2] / "target/i386/translate.c"
MPX_HELPER = Path(__file__).resolve().parents[2] / "target/i386/mpx_helper.c"

# Helpers whose implementation performs a guest memory access without a
# translator-visible tcg_gen_qemu_* primitive.  Their caller owns one exact
# event after the helper returns.
HELPER_MEMORY_PRODUCERS = {
    "gen_helper_bndldx32",
    "gen_helper_bndldx64",
    "gen_helper_bndstx32",
    "gen_helper_bndstx64",
    "gen_helper_cmpxchg8b",
    "gen_helper_cmpxchg8b_unlocked",
    "gen_helper_cmpxchg16b",
    "gen_helper_cmpxchg16b_unlocked",
    "gen_helper_fbld_ST0",
    "gen_helper_fbst_ST0",
    "gen_helper_fldenv",
    "gen_helper_fldt_ST0",
    "gen_helper_frstor",
    "gen_helper_fsave",
    "gen_helper_fstenv",
    "gen_helper_fstt_ST0",
    "gen_helper_fxsave",
    "gen_helper_fxrstor",
    "gen_helper_xsave",
    "gen_helper_xsaveopt",
    "gen_helper_xrstor",
}

HELPER_SELF_INSTRUMENTED = {
    "gen_helper_bndldx32",
    "gen_helper_bndldx64",
    "gen_helper_bndstx32",
    "gen_helper_bndstx64",
}


def next_break(lines, start, limit):
    """Return the first opcode break after start, or limit."""
    for i in range(start, min(limit, len(lines))):
        if re.search(r"\bbreak\s*;", lines[i]):
            return i + 1
    return min(limit, len(lines))


def event_window(lines, start, limit):
    stop = next_break(lines, start, limit)
    return stop, "".join(lines[start:stop])


def fail(errors, line, message):
    errors.append(f"translate.c:{line + 1}: {message}")


def function_body(text, name):
    """Return one C function body by brace matching, or None."""
    match = re.search(rf"\b{name}\s*\([^;]*?\)\s*\{{", text, re.S)
    if match is None:
        return None
    depth = 1
    pos = match.end()
    while pos < len(text) and depth:
        if text[pos] == "{":
            depth += 1
        elif text[pos] == "}":
            depth -= 1
        pos += 1
    return text[match.end():pos - 1] if depth == 0 else None


def main():
    try:
        lines = TRANSLATE.read_text().splitlines(keepends=True)
    except OSError as exc:
        print(f"semantic inventory: cannot read {TRANSLATE}: {exc}", file=sys.stderr)
        return 2

    errors = []
    direct_count = 0
    helper_count = 0
    atomic_count = 0
    helper_names_seen = set()
    direct_pattern = re.compile(r"\btcg_gen_qemu_(?:ld|st)\w*\s*\(")
    atomic_pattern = re.compile(r"\btcg_gen_atomic_\w*\s*\(")
    helper_pattern = re.compile(
        r"\b(?:" + "|".join(map(re.escape, sorted(HELPER_MEMORY_PRODUCERS))) + r")\s*\(")

    for i, line in enumerate(lines):
        if direct_pattern.search(line):
            direct_count += 1
            _, window = event_window(lines, i + 1, i + 64)
            # Raw wrappers may publish the invalidation and have their F01
            # aggregate emitted by the immediate class wrapper.  Either event
            # is enough to prove this primitive is on the shared surface.
            if "gen_sem_" not in window:
                fail(errors, i, "direct guest-memory primitive has no semantic event")
            elif "gen_sem_on_store_class" not in window and \
                    "gen_sem_mem_access" not in window:
                fail(errors, i, "direct primitive event is not an access/overwrite event")
            elif "_class" not in window and "cls" not in window:
                fail(errors, i, "direct primitive event does not carry SemOpClass")

        if atomic_pattern.search(line):
            atomic_count += 1
            # gen_op() shares one F01 epilogue across its switch cases, so
            # the event can follow the case-local break.  Keep this bounded
            # to the containing helper-sized region.
            window = "".join(lines[i + 1:i + 160])
            if "gen_sem_on_store_class" not in window or \
                    "gen_sem_mem_access_f01_class" not in window:
                fail(errors, i, "TCG atomic producer lacks typed post-success event")

        if helper_pattern.search(line):
            helper_count += 1
            helper_name = helper_pattern.search(line).group(0).split("(")[0]
            helper_names_seen.add(helper_name)
            if helper_name in HELPER_SELF_INSTRUMENTED:
                continue
            _, window = event_window(lines, i + 1, i + 96)
            if "gen_sem_" not in window:
                fail(errors, i, "helper-backed memory producer has no semantic event")
            elif "gen_sem_mem_access" not in window and \
                    "gen_sem_mem_overwrite" not in window:
                fail(errors, i, "helper producer event is not an access/overwrite event")
            elif "_class" not in window and "SEM_OP_" not in window:
                fail(errors, i, "helper producer event does not carry SemOpClass")

    # Keep this gate meaningful if the translator is substantially rewritten:
    # an empty scan is never accepted as complete coverage.
    if direct_count < 20:
        errors.append(f"only {direct_count} direct guest-memory primitives found")
    missing_helpers = sorted(HELPER_MEMORY_PRODUCERS - helper_names_seen)
    if missing_helpers:
        errors.append(
            "helper-backed producer names missing from translator: "
            + ", ".join(missing_helpers)
        )

    try:
        mpx_text = MPX_HELPER.read_text()
    except OSError as exc:
        errors.append(f"cannot read {MPX_HELPER}: {exc}")
    else:
        for emitted_name in sorted(HELPER_SELF_INSTRUMENTED):
            helper_name = emitted_name.removeprefix("gen_")
            body = function_body(mpx_text, helper_name)
            if body is None:
                errors.append(f"{helper_name} body missing from mpx_helper.c")
            elif "sem_mem_helper_access" not in body:
                errors.append(
                    f"{helper_name} lacks its self-instrumented semantic event"
                )

    if errors:
        print("semantic inventory: FAIL", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1

    print(
        f"PASS semantic inventory ({direct_count} direct primitives, "
        f"{atomic_count} atomic primitives, "
        f"{helper_count} helper-backed producers)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
