#!/usr/bin/env python3
"""Bounded sanity-check of the Stage-2.2 semantic producer inventory.

The checker rejects manifest tokens with no source callsite, discovers direct
translator primitives and memory-owning generated helpers, and checks their
nearby shared-event surface.  It is not a C compiler: indirect dispatch,
control-flow ordering, class agreement, and exact event cardinality still
require the runtime fixtures and review.
"""

from pathlib import Path
import re
import sys


TRANSLATE = Path(__file__).resolve().parents[2] / "target/i386/translate.c"
MPX_HELPER = Path(__file__).resolve().parents[2] / "target/i386/mpx_helper.c"
FPU_HELPER = Path(__file__).resolve().parents[2] / "target/i386/fpu_helper.c"
MEM_HELPER = Path(__file__).resolve().parents[2] / "target/i386/mem_helper.c"
SEG_HELPER = Path(__file__).resolve().parents[2] / "target/i386/seg_helper.c"
OPS_SSE = Path(__file__).resolve().parents[2] / "target/i386/ops_sse.h"
SEM_EVENTS = Path(__file__).resolve().parents[2] / "linux-user/sem-events.c"
SYMBOLIC = Path(__file__).resolve().parents[2] / "tcg/symbolic/symbolic.c"
SYSCALL = Path(__file__).resolve().parents[2] / "linux-user/syscall.c"
SNAPSHOT = Path(__file__).resolve().parents[2] / "linux-user/snapshot.c"
SIGNAL = Path(__file__).resolve().parents[2] / "linux-user/i386/signal.c"

HELPER_SOURCES = (MEM_HELPER, MPX_HELPER, FPU_HELPER, SEG_HELPER, OPS_SSE)
SOURCE_FILES = (TRANSLATE, MPX_HELPER, FPU_HELPER, MEM_HELPER, SEG_HELPER,
                OPS_SSE, SYMBOLIC, SYSCALL, SNAPSHOT, SIGNAL)


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


def producer_manifest(text):
    """Parse the macro rows in sem_producer_table.

    Coverage is intentionally a comma-separated list of source symbols.  An
    optional colon suffix documents an unsupported row without affecting the
    symbol used for linkage.
    """
    start = text.index("const SemProducerSpec sem_producer_table")
    end = text.index("#undef UNSUPPORTED", start)
    section = text[start:end]
    rows = []
    for match in re.finditer(
            r"\b(PRODUCER|DYNAMIC_PRODUCER|UNSUPPORTED)\s*\(", section):
        pos = match.end()
        depth = 1
        while pos < len(section) and depth:
            if section[pos] == "(":
                depth += 1
            elif section[pos] == ")":
                depth -= 1
            pos += 1
        if depth:
            continue
        strings = re.findall(r'"([^"\\]*(?:\\.[^"\\]*)*)"',
                             section[match.end():pos - 1])
        if len(strings) < 2:
            continue
        rows.append((strings[0], strings[-1], match.group(1)))
    return rows


def helper_body_sources():
    """Load helper implementations once for direct-memory classification."""
    return [(path, path.read_text()) for path in HELPER_SOURCES]


def direct_memory_helper(body):
    """Conservative detector for helper-owned guest-memory operations."""
    return re.search(
        r"\b(?:cpu_(?:ld|st)[a-z0-9_]*|"
        r"helper_atomic_[a-z0-9_]*_mmu|"
        r"(?:ld|st)[bwlq](?:_[a-z0-9]+)?_p\b|"
        r"(?:ld|st)[bwlq]_data(?:_[a-z0-9]+)?\b|"
        r"(?:PUSH|POP)[WLQ]_RA\b|"
        r"\b(?:load_segment_ra|helper_ret_protected)\s*\()",
        body,
    ) is not None


def helper_owns_memory(name, sources, seen=None):
    """Resolve the small helper-call graph to catch memory-owning wrappers."""
    if seen is None:
        seen = set()
    if name in seen:
        return False
    seen.add(name)
    body = None
    for _, text in sources:
        body = function_body(text, name)
        if body is not None:
            break
    if body is None:
        return False
    if direct_memory_helper(body):
        return True
    callees = re.findall(r"\b(helper_[A-Za-z0-9_]+|load_segment_ra|"
                         r"check_io|do_[A-Za-z0-9_]+)\s*\(", body)
    return any(helper_owns_memory(callee, sources, seen)
               for callee in callees)


def main():
    try:
        lines = TRANSLATE.read_text().splitlines(keepends=True)
        source_text = "\n".join(path.read_text() for path in SOURCE_FILES)
        manifest_rows = producer_manifest(SEM_EVENTS.read_text())
        helper_sources = helper_body_sources()
    except OSError as exc:
        print(f"semantic inventory: cannot read {TRANSLATE}: {exc}", file=sys.stderr)
        return 2
    except ValueError as exc:
        print(f"semantic inventory: cannot parse producer table: {exc}",
              file=sys.stderr)
        return 2

    errors = []
    direct_count = 0
    helper_count = 0
    atomic_count = 0
    direct_pattern = re.compile(r"\btcg_gen_qemu_(?:ld|st)\w*\s*\(")
    atomic_pattern = re.compile(r"\btcg_gen_atomic_\w*\s*\(")
    helper_pattern = re.compile(r"\bgen_helper_([A-Za-z0-9_]+)\s*\(")

    if not manifest_rows:
        errors.append("producer manifest is empty")
    manifest_helper_names = set()
    unsupported_helper_names = set()
    for producer, coverage, row_kind in manifest_rows:
        symbols = [item.strip().split(":", 1)[0].strip()
                   for item in coverage.split(",") if item.strip()]
        if not symbols:
            errors.append(f"{producer}: coverage has no source symbol")
        for symbol in symbols:
            if not re.search(r"\b" + re.escape(symbol) + r"\b",
                             source_text):
                errors.append(
                    f"{producer}: coverage symbol {symbol} is absent from source")
            if symbol.startswith("gen_helper_"):
                manifest_helper_names.add(symbol)
                if row_kind == "UNSUPPORTED":
                    unsupported_helper_names.add(symbol)
        if row_kind == "UNSUPPORTED" and not coverage.split(":", 1)[0].strip():
            errors.append(f"{producer}: unsupported row has no coverage symbol")

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

        helper_match = helper_pattern.search(line)
        if helper_match:
            helper_name = "gen_helper_" + helper_match.group(1)
            helper_impl = "helper_" + helper_match.group(1)
            body = None
            for _, helper_text in helper_sources:
                body = function_body(helper_text, helper_impl)
                if body is not None:
                    break
            owns_memory = helper_owns_memory(helper_impl, helper_sources)
            if owns_memory and helper_name not in manifest_helper_names:
                fail(errors, i,
                     f"helper {helper_name} owns guest memory but is not in manifest")
            if helper_name not in manifest_helper_names:
                continue
            helper_count += 1
            if helper_name in unsupported_helper_names:
                _, window = event_window(lines, i + 1, i + 128)
                if "gen_sem_mem_unsupported" not in window:
                    fail(errors, i,
                         "unsupported helper lacks fail-closed semantic event")
                continue
            # Self-instrumented helpers publish only from their body.  All
            # translator-owned helpers must have a nearby typed post-success
            # event; the bounded window ends at the opcode break.
            if body is not None and re.search(r"\bsem_[a-z_]+\s*\(", body):
                continue
            _, window = event_window(lines, i + 1, i + 128)
            if "gen_sem_" not in window:
                fail(errors, i, "helper-backed producer has no semantic event")
            elif "gen_sem_mem_access" not in window and \
                    "gen_sem_mem_overwrite" not in window and \
                    "gen_sem_mem_unsupported" not in window:
                fail(errors, i, "helper producer event is not an access/overwrite event")
            elif "_class" not in window and "SEM_OP_" not in window and \
                    "unsupported" not in window:
                fail(errors, i, "helper producer event does not carry SemOpClass")

    # Keep this gate meaningful if the translator is substantially rewritten:
    # an empty scan is never accepted as complete coverage.
    if direct_count < 20:
        errors.append(f"only {direct_count} direct guest-memory primitives found")
    # Every helper token declared by a supported/unsupported row must be
    # present as an actual translated helper or dispatch-table entry.
    for helper_name in sorted(manifest_helper_names):
        if not re.search(r"\b" + re.escape(helper_name) + r"\b", source_text):
            errors.append(f"manifest helper {helper_name} is absent from source")

    if errors:
        print("semantic inventory: FAIL", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1

    print(
        f"PASS semantic inventory sanity check "
        f"({len(manifest_rows)} manifest families, "
        f"{direct_count} direct primitives, {atomic_count} atomic primitives, "
        f"{helper_count} classified helper callsites)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
