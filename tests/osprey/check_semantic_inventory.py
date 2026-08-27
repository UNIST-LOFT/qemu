#!/usr/bin/env python3
"""Structural Stage-2.2 semantic producer inventory gate.

The checker resolves every manifest coverage token to a real translator
callsite, helper body, generated helper, or explicit target/file gate.  It
then assigns direct TCG memory and atomic operations to their containing
function/switch region and requires the actual semantic emission in that
region.  Memory-owning helper callsites are resolved transitively; supported
helpers require an access emission or self-instrumented event, while
unsupported helpers and privilege-dependent helper files require an explicit
fail-closed boundary.  The emitted wrapper and class are checked at the
source callsite, so a producer cannot silently publish under another class.

This is intentionally a source-level gate, not a C compiler: exact runtime
fault ordering and multipart cardinality remain covered by the deterministic
fixtures.
"""

import re
import sys
from pathlib import Path

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


def fail(errors, line, message):
    errors.append(f"translate.c:{line + 1}: {message}")


def function_body(text, name):
    """Return one C function body by brace matching, or None.

    Resolves the ops_sse.h glue(helper_X, SUFFIX) definition form to the
    helper_X symbol so generated helpers are found by their manifest name.
    """
    match = re.search(rf"\b{re.escape(name)}\s*\([^;]*?\)\s*\{{", text, re.DOTALL)
    if match is None:
        match = re.search(
            rf"\bglue\(\s*{re.escape(name)}\s*,\s*[A-Za-z0-9_]+\s*\)"
            rf"\s*\([^;]*?\)\s*\{{", text, re.DOTALL)
    if match is None:
        # ops_sse.h instantiates glue(helper_maskmov, SUFFIX) as
        # helper_maskmov_mmx / helper_maskmov_xmm.
        suffix_match = re.fullmatch(r"(helper_[A-Za-z0-9_]+)_(mmx|xmm)",
                                    name)
        if suffix_match is not None:
            match = re.search(
                rf"\bglue\(\s*{re.escape(suffix_match.group(1))}\s*,"
                rf"\s*SUFFIX\s*\)\s*\([^;]*?\)\s*\{{", text, re.DOTALL)
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


def split_args(section):
    """Split a macro argument list on top-level commas (quote-aware)."""
    args = []
    depth = 0
    start = 0
    in_string = False
    for i, ch in enumerate(section):
        if ch == '"' and not in_string:
            in_string = True
        elif ch == '"' and in_string:
            in_string = False
        elif not in_string:
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
            elif ch == "," and depth == 0:
                args.append(section[start:i].strip())
                start = i + 1
    args.append(section[start:].strip())
    return args


def producer_manifest(text):
    """Parse the macro rows in sem_producer_table.

    Coverage is intentionally a comma-separated list of source symbols.  An
    optional colon suffix documents an unsupported row without affecting the
    symbol used for linkage.  Returns (name, class-or-None, policy-or-None,
    width-array-or-None, coverage, kind).
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
        args = split_args(section[match.end():pos - 1])
        kind = match.group(1)
        expected_args = {
            "PRODUCER": 6,
            "DYNAMIC_PRODUCER": 3,
            "UNSUPPORTED": 2,
        }[kind]
        if len(args) != expected_args:
            raise ValueError(
                f"{kind} row has {len(args)} arguments, expected "
                f"{expected_args}")
        name = args[0].strip('"')
        coverage = args[-1].strip('"')
        if kind == "UNSUPPORTED":
            rows.append((name, None, None, None, coverage, kind))
        elif kind == "DYNAMIC_PRODUCER":
            rows.append((name, args[1], "SEM_INTERVAL_DYNAMIC", None,
                         coverage, kind))
        else:
            rows.append((name, args[1], args[2], args[3], coverage, kind))
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


def helper_body_has_class(name, class_token, sources, seen=None):
    """True when the helper body (or a transitively called helper) carries
    the manifest SemOpClass token.  Self-instrumented helpers publish their
    class from the body; translator-instrumented helpers carry it in the
    callsite window instead."""
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
    if class_token in body:
        return True
    callees = re.findall(r"\b(helper_[A-Za-z0-9_]+|sem_[A-Za-z0-9_]+|"
                         r"do_[A-Za-z0-9_]+)\s*\(", body)
    return any(helper_body_has_class(callee, class_token, sources, seen)
               for callee in callees)


def helper_callees(body):
    """Return helper and known static-wrapper calls from one body."""
    return set(re.findall(
        r"\b(helper_[A-Za-z0-9_]+|load_segment_ra|helper_ret_protected|"
        r"check_io|do_[A-Za-z0-9_]+)\s*\(", body))


def mask_c_source(text):
    """Blank comments and literals while preserving source positions."""
    out = list(text)
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
            continue
        if text.startswith("/*", i):
            j = text.find("*/", i + 2)
            j = n - 2 if j < 0 else j
            for k in range(i, j + 2):
                if out[k] != "\n":
                    out[k] = " "
            i = j + 2
            continue
        if text[i] in ('\"', "'"):
            quote = text[i]
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == quote:
                    j += 1
                    break
                j += 1
            for k in range(i, min(j, n)):
                if out[k] != "\n":
                    out[k] = " "
            i = j
            continue
        i += 1
    return "".join(out)


def matching_brace(text, opening):
    """Return the closing brace for an already-masked source."""
    depth = 1
    for pos in range(opening + 1, len(text)):
        if text[pos] == "{":
            depth += 1
        elif text[pos] == "}":
            depth -= 1
            if depth == 0:
                return pos
    return None


def function_spans(text):
    """Find ordinary C function bodies with source offsets.

    This deliberately operates on a comment/string-masked source, so a
    producer is assigned to its actual containing function rather than to a
    fixed number of following lines.  Macro-generated helper definitions are
    handled by function_body() separately.
    """
    masked = mask_c_source(text)
    spans = []
    keywords = {"if", "for", "while", "switch", " do", "else", "catch"}
    for opening, char in enumerate(masked):
        if char != "{":
            continue
        close = matching_brace(masked, opening)
        if close is None:
            continue
        prefix_start = max(masked.rfind("}", 0, opening),
                           masked.rfind(";", 0, opening),
                           masked.rfind("{", 0, opening)) + 1
        prefix = masked[prefix_start:opening]
        paren = prefix.rfind(")")
        if paren < 0:
            continue
        depth = 1
        left = paren - 1
        while left >= 0:
            if masked[prefix_start + left] == ")":
                depth += 1
            elif masked[prefix_start + left] == "(":
                depth -= 1
                if depth == 0:
                    break
            left -= 1
        if left < 0:
            continue
        name_match = re.search(r"([A-Za-z_][A-Za-z0-9_]*)\s*$",
                               prefix[:left])
        if name_match is None:
            continue
        name = name_match.group(1)
        if name in keywords or name in {"glue"}:
            continue
        spans.append((name, prefix_start, opening + 1, close))
    return spans


def enclosing_span(spans, pos):
    """Return the innermost ordinary function containing pos."""
    candidates = [span for span in spans if span[2] <= pos < span[3]]
    return min(candidates, key=lambda span: span[3] - span[2]) \
        if candidates else None


def call_sites(text, pattern):
    """Return (name, start, end) for calls matching a token regex."""
    masked = mask_c_source(text)
    result = []
    for match in re.finditer(pattern, masked):
        opening = masked.find("(", match.start(), match.end())
        if opening < 0:
            continue
        depth = 1
        pos = opening + 1
        while pos < len(masked) and depth:
            if masked[pos] == "(":
                depth += 1
            elif masked[pos] == ")":
                depth -= 1
            pos += 1
        if depth == 0:
            result.append((match.group(1), match.start(), pos))
    return result


def parse_coverage_tokens(coverage):
    """Split coverage into source tokens and its optional reason suffix."""
    tokens = []
    for item in coverage.split(","):
        item = item.strip()
        if not item:
            continue
        token = item.split(":", 1)[0].strip()
        tokens.append(token)
    return tokens


def next_case_label(masked, start, limit):
    """Return the next switch-label boundary after a producer call."""
    match = re.search(r"\b(?:case\b[^:]*:|default\s*:)",
                      masked[start:min(limit, len(masked))])
    return start + match.start() if match else limit


def source_line(text, pos):
    return text.count("\n", 0, pos) + 1


def event_arguments(event_text):
    """Return top-level arguments from one semantic-event call."""
    opening = event_text.find("(")
    if opening < 0 or not event_text.endswith(")"):
        return []
    return split_args(event_text[opening + 1:-1])


def event_class_token(event_name, event_text):
    """Resolve literal class arguments; the plain wrapper defaults integer."""
    match = re.search(r"\b(SEM_OP_[A-Z0-9_]+)\b", event_text)
    if match:
        return match.group(1)
    if event_name == "gen_sem_mem_access":
        return "SEM_OP_INTEGER"
    return None


def event_literal_width(event_name, event_text):
    """Resolve a constant F01 width where the wrapper exposes one."""
    args = event_arguments(event_text)
    if len(args) < 2:
        return None
    if event_name == "gen_sem_mem_access_f01_raw_class":
        return int(args[1]) if args[1].isdigit() else None
    if event_name in ("gen_sem_mem_access_class", "gen_sem_mem_access_f01_class"):
        return {
            "MO_8": 1, "MO_16": 2, "MO_32": 4, "MO_64": 8,
            "MO_128": 16,
        }.get(args[1])
    return None


def event_sites(text):
    """Find actual translator semantic-event emission calls."""
    return call_sites(
        text,
        r"\b(gen_sem_mem_access(?:_f01_raw_class|_f01_class|_class|"
        r"_flags_class|_f01_auto_class)?|gen_sem_mem_unsupported)\s*\(",
    )


def memory_body_calls(text):
    """Find helper-owned guest-memory primitive calls, not declarations."""
    return call_sites(
        text,
        r"\b((?:cpu_(?:ld|st)[A-Za-z0-9_]*|"
        r"helper_atomic_[A-Za-z0-9_]*_mmu|"
        r"(?:ld|st)[bwlq](?:_[A-Za-z0-9]+)?_p|"
        r"(?:ld|st)[bwlq]_data(?:_[A-Za-z0-9]+)?|"
        r"PUSH[WLQ]_RA|POP[WLQ]_RA|"
        r"load_segment_ra|helper_ret_protected))\s*\(",
    )


def main():
    try:
        translate_text = TRANSLATE.read_text()
        source_file_texts = [(path, path.read_text()) for path in SOURCE_FILES]
        source_text = "\n".join(text for _, text in source_file_texts)
        manifest_rows = producer_manifest(SEM_EVENTS.read_text())
        helper_sources = helper_body_sources()
    except OSError as exc:
        print(f"semantic inventory: cannot read {TRANSLATE}: {exc}",
              file=sys.stderr)
        return 2
    except ValueError as exc:
        print(f"semantic inventory: cannot parse producer table: {exc}",
              file=sys.stderr)
        return 2

    errors = []
    direct_count = 0
    helper_count = 0
    atomic_count = 0
    if not manifest_rows:
        errors.append("producer manifest is empty")
    manifest_helper_names = set()
    manifest_class = {}
    unsupported_helper_names = set()
    manifest_file_tokens = set()
    manifest_target_tokens = set()
    manifest_policies = {}
    manifest_producers = set()
    dynamic_specs = []
    width_arrays = {}
    manifest_text = SEM_EVENTS.read_text()
    for match in re.finditer(
            r"static\s+const\s+uint32_t\s+(\w+)\[\]\s*=\s*\{([^}]*)\}",
            manifest_text, re.DOTALL):
        width_arrays[match.group(1)] = {
            int(value) for value in re.findall(r"\b\d+\b", match.group(2))
        }
    manifest_widths = {}
    for (producer, class_token, policy_token, width_array,
         coverage, row_kind) in manifest_rows:
        if producer in manifest_producers:
            errors.append(f"duplicate producer manifest row {producer}")
        manifest_producers.add(producer)
        if row_kind != "UNSUPPORTED":
            manifest_policies.setdefault(class_token, set()).add(policy_token)
            manifest_widths.setdefault(class_token, set()).update(
                width_arrays.get(width_array, set()))

        symbols = parse_coverage_tokens(coverage)
        if not symbols:
            errors.append(f"{producer}: coverage has no source symbol")
        for symbol in symbols:
            if symbol.startswith("file="):
                filename = symbol[len("file="):]
                if not any(path.name == filename for path, _ in source_file_texts):
                    errors.append(
                        f"{producer}: coverage file {filename} is absent")
                manifest_file_tokens.add(filename)
            elif symbol.startswith("target="):
                # Target gates are explicit inventory entries, not symbols
                # expected to occur in C source.  The current checker runs
                # against the x86-64 user target.
                if symbol[len("target="):] != "x86_64":
                    errors.append(
                        f"{producer}: unsupported target gate is not x86_64")
                manifest_target_tokens.add(symbol[len("target="):])
            elif symbol.startswith("gen_helper_"):
                # Every manifest helper must be reachable from the
                # translator: a definition in a helper source file alone
                # does not prove a producer callsite exists.
                if not re.search(r"\b" + re.escape(symbol) + r"\b",
                                  translate_text):
                    errors.append(
                        f"{producer}: helper {symbol} is absent from translate.c")
                manifest_helper_names.add(symbol)
                manifest_class[symbol] = class_token
                if row_kind == "UNSUPPORTED":
                    unsupported_helper_names.add(symbol)
            elif not re.search(r"\b" + re.escape(symbol) + r"\b",
                               source_text):
                errors.append(
                    f"{producer}: coverage symbol {symbol} is absent from source")
        if row_kind == "DYNAMIC_PRODUCER":
            coverage_files = {
                symbol[len("file="):]
                for symbol in symbols if symbol.startswith("file=")
            }
            coverage_events = {
                symbol for symbol in symbols
                if symbol in {"sem_mem_overwrite", "sem_context_replace"}
            }
            if not coverage_files:
                errors.append(
                    f"{producer}: dynamic producer lacks a coverage file")
            if "sem_mem_overwrite" not in coverage_events:
                errors.append(
                    f"{producer}: dynamic producer lacks a class-carrying "
                    "overwrite event")
            dynamic_specs.append((producer, class_token, coverage_files,
                                  coverage_events))
        if row_kind == "UNSUPPORTED":
            if ":" not in coverage:
                errors.append(
                    f"{producer}: unsupported row lacks a colon-suffixed reason")
            else:
                reason = coverage.split(":", 1)[1].strip()
                if len(reason) < 8:
                    errors.append(
                        f"{producer}: unsupported row reason is not concrete")

    # Dynamic non-translator families carry their owning files and event APIs
    # in the manifest itself.  Bind every callsite back to exactly one row so
    # a malformed DYNAMIC_PRODUCER parser or a wrong literal class cannot make
    # the structural gate silently omit model/syscall/mapping/signal/snapshot
    # producers again.
    source_by_name = {path.name: text for path, text in source_file_texts}
    for producer, class_token, coverage_files, coverage_events in dynamic_specs:
        seen_events = set()
        for filename in coverage_files:
            file_text = source_by_name.get(filename)
            if file_text is None:
                continue
            file_has_class = False
            for event_name, event_start, event_end in call_sites(
                    file_text,
                    r"\b(sem_mem_overwrite|sem_context_replace)\s*\("):
                if event_name not in coverage_events:
                    continue
                seen_events.add(event_name)
                if event_name == "sem_mem_overwrite":
                    event_text = file_text[event_start:event_end]
                    if event_class_token(event_name, event_text) == class_token:
                        file_has_class = True
            if not file_has_class:
                errors.append(
                    f"{producer}: {filename} has no sem_mem_overwrite call "
                    f"with class {class_token}")
        missing_events = coverage_events - seen_events
        for event_name in sorted(missing_events):
            errors.append(
                f"{producer}: coverage event {event_name} is absent from "
                "its declared files")

    dynamic_event_count = 0
    dynamic_files = set().union(
        *(coverage_files for _, _, coverage_files, _ in dynamic_specs)) \
        if dynamic_specs else set()
    for filename in dynamic_files:
        file_text = source_by_name.get(filename)
        if file_text is None:
            continue
        for event_name, event_start, event_end in call_sites(
                file_text,
                r"\b(sem_mem_overwrite|sem_context_replace)\s*\("):
            dynamic_event_count += 1
            class_token = None
            if event_name == "sem_mem_overwrite":
                event_text = file_text[event_start:event_end]
                class_token = event_class_token(event_name, event_text)
                if class_token is None:
                    errors.append(
                        f"{filename}:{source_line(file_text, event_start)}: "
                        "dynamic overwrite lacks a literal SemOpClass")
                    continue
            matches = [
                producer for producer, expected_class, coverage_files,
                coverage_events in dynamic_specs
                if filename in coverage_files and event_name in coverage_events
                and (class_token is None or class_token == expected_class)
            ]
            if len(matches) != 1:
                errors.append(
                    f"{filename}:{source_line(file_text, event_start)}: "
                    f"{event_name} binds to {len(matches)} dynamic manifest "
                    "rows")

    masked_translate = mask_c_source(translate_text)
    translate_spans = function_spans(translate_text)
    emitted_events = event_sites(translate_text)

    # Literal widths in translator events must belong to the manifest class.
    # Dynamic `TCGMemOp`/helper widths are checked by the runtime fixtures and
    # the C manifest's complete width arrays rather than guessed here.
    literal_event_count = 0
    for event_name, event_start, event_end in emitted_events:
        event_text = translate_text[event_start:event_end]
        if event_name == "gen_sem_mem_unsupported":
            continue
        class_token = event_class_token(event_name, event_text)
        if class_token is None:
            continue  # auto-class wrapper carries a runtime class parameter
        if class_token not in manifest_policies:
            fail(errors, source_line(translate_text, event_start) - 1,
                 f"event {event_name} uses unmanifested class {class_token}")
            continue
        width = event_literal_width(event_name, event_text)
        if width is not None:
            literal_event_count += 1
            if width not in manifest_widths.get(class_token, set()):
                fail(errors, source_line(translate_text, event_start) - 1,
                     f"event {event_name} width {width} is absent from "
                     f"manifest class {class_token}")

    # Helper-owned publishers carry the policy in the API they call: sparse
    # MASKMOV, multipart MPX transactions, sparse XSAVE components, and
    # single-interval helper accesses.  Check their literal class/width
    # arguments against the same manifest, without maintaining another list
    # of producer names.
    helper_event_count = 0
    helper_policy_requirements = {
        "sem_mem_maskmov": {"SEM_INTERVAL_SPARSE"},
        "sem_mem_helper_access_part": {
            "SEM_INTERVAL_MULTIPART", "SEM_INTERVAL_SPARSE",
        },
        "sem_mem_helper_access": {"SEM_INTERVAL_EXACT_WIDTH"},
    }
    for path, helper_text in helper_sources:
        for event_name, event_start, event_end in call_sites(
                helper_text,
                r"\b(sem_mem_maskmov|sem_mem_helper_access_part|"
                r"sem_mem_helper_access)\s*\("):
            event_text = helper_text[event_start:event_end]
            class_token = event_class_token(event_name, event_text)
            if class_token is None:
                continue
            helper_event_count += 1
            policies = manifest_policies.get(class_token, set())
            required = helper_policy_requirements[event_name]
            if not policies.intersection(required):
                errors.append(
                    f"{path.name}:{source_line(helper_text, event_start)}: "
                    f"{event_name} class {class_token} lacks required "
                    f"interval policy")
            args = event_arguments(event_text)
            if event_name != "sem_mem_maskmov" and len(args) > 2:
                size = int(args[2]) if args[2].isdigit() else None
                if size is not None and size not in manifest_widths.get(
                        class_token, set()):
                    errors.append(
                        f"{path.name}:{source_line(helper_text, event_start)}: "
                        f"{event_name} width {size} is absent from manifest "
                        f"class {class_token}")

    # Direct TCG memory operations are tied to the semantic emission in the
    # same function/switch region.  A later unrelated event in disas_insn
    # cannot satisfy a producer in another case, and an event before an
    # unsupported helper is still accepted because rejection deliberately
    # precedes a helper that may fault.
    direct_calls = call_sites(
        translate_text, r"\b(tcg_gen_qemu_(?:ld|st)[A-Za-z0-9_]*)\s*\(")
    atomic_calls = call_sites(
        translate_text, r"\b(tcg_gen_atomic_[A-Za-z0-9_]*)\s*\(")
    direct_count = len(direct_calls)
    atomic_count = len(atomic_calls)

    def region_for(pos, span):
        start = span[2]
        labels = list(re.finditer(
            r"\b(?:case\b[^:]*:|default\s*:)",
            masked_translate[start:pos]))
        if labels:
            start += labels[-1].start()
        end = next_case_label(masked_translate, pos, span[3])
        return start, end

    def events_in_region(start, end):
        return [event for event in emitted_events
                if start <= event[1] < end]

    for name, start, end in direct_calls:
        span = enclosing_span(translate_spans, start)
        if span is None:
            fail(errors, source_line(translate_text, start) - 1,
                 f"{name} is outside a recognized translator function")
            continue
        region_start, region_end = region_for(start, span)
        candidates = [event for event in events_in_region(region_start, region_end)
                      if event[1] >= end]
        if not candidates:
            # The raw store wrapper intentionally owns only shadow
            # invalidation; its typed F01 event is emitted by the enclosing
            # gen_op_st_v_class wrapper after the call returns.
            if span[0] == "gen_op_st_v_raw_class":
                callers = [candidate for candidate in translate_spans
                           if candidate[0] == "gen_op_st_v_class" and
                           "gen_op_st_v_raw_class" in
                           translate_text[candidate[2]:candidate[3]] and
                           "gen_sem_mem_access_f01_auto_class" in
                           translate_text[candidate[2]:candidate[3]]]
                if callers:
                    continue
            fail(errors, source_line(translate_text, start) - 1,
                 f"{name} has no post-success semantic emission in its case")
            continue
        event_name, event_start, event_end = candidates[0]
        event_text = translate_text[event_start:event_end]
        if event_name != "gen_sem_mem_unsupported" and \
                "gen_sem_mem_access" not in event_name:
            fail(errors, source_line(translate_text, start) - 1,
                 f"{name} is paired with non-access event {event_name}")
        # `gen_sem_mem_access` is the typed default INTEGER wrapper.  Every
        # other access wrapper carries either a literal class or the `cls`
        # parameter through the actual emission call.
        if event_name != "gen_sem_mem_unsupported" and \
                event_name != "gen_sem_mem_access" and \
                "SEM_OP_" not in event_text and "cls" not in event_text:
            fail(errors, source_line(translate_text, start) - 1,
                 f"{name} emission {event_name} has no SemOpClass")

    for name, start, end in atomic_calls:
        span = enclosing_span(translate_spans, start)
        if span is None:
            fail(errors, source_line(translate_text, start) - 1,
                 f"{name} is outside a recognized translator function")
            continue
        # gen_op() has one shared post-switch epilogue, so its event is
        # intentionally outside the individual case label.  The containing
        # function is the tightest valid structural boundary here.
        region_start, region_end = span[2], span[3]
        candidates = [event for event in events_in_region(region_start, region_end)
                      if event[1] >= end]
        if not candidates:
            fail(errors, source_line(translate_text, start) - 1,
                 f"{name} has no post-success F01 emission in its function")
            continue
        event_name, _event_start, event_end = candidates[0]
        region_text = translate_text[start:event_end]
        if (event_name != "gen_sem_mem_access_f01_class" or
                "SEM_OP_ATOMIC_RMW" not in region_text):
            fail(errors, source_line(translate_text, start) - 1,
                 f"{name} lacks a typed ATOMIC_RMW F01 emission")

    helper_calls = call_sites(
        translate_text, r"\b(gen_helper_[A-Za-z0-9_]+)\s*\(")
    for helper_name, start, _end in helper_calls:
        helper_impl = "helper_" + helper_name[len("gen_helper_"):]
        body = None
        for _, helper_text in helper_sources:
            body = function_body(helper_text, helper_impl)
            if body is not None:
                break
        owns_memory = helper_owns_memory(helper_impl, helper_sources)
        if owns_memory and helper_name not in manifest_helper_names:
            fail(errors, source_line(translate_text, start) - 1,
                 f"helper {helper_name} owns guest memory but is not in manifest")
        if helper_name not in manifest_helper_names:
            continue
        helper_count += 1
        span = enclosing_span(translate_spans, start)
        if span is None:
            fail(errors, source_line(translate_text, start) - 1,
                 f"helper {helper_name} is outside a recognized translator function")
            continue
        region_start, region_end = region_for(start, span)
        region_events = events_in_region(region_start, region_end)
        if helper_name in unsupported_helper_names:
            if not any(event[0] == "gen_sem_mem_unsupported"
                       for event in region_events):
                fail(errors, source_line(translate_text, start) - 1,
                     f"unsupported helper {helper_name} lacks fail-closed emission")
            continue
        # Helpers with their own guest-memory event publish from the helper
        # body; translator-owned helpers publish in this exact switch region.
        if body is not None and re.search(r"\bsem_[a-z_]+\s*\(", body):
            continue
        if not any(event[0].startswith("gen_sem_mem_access")
                   for event in region_events):
            fail(errors, source_line(translate_text, start) - 1,
                 f"helper {helper_name} lacks an access emission in its case")

    # Every reachable helper that owns memory must be represented by a
    # manifest token.  This closes the gap where a helper definition exists
    # but no translator callsite was listed.
    referenced_owned = set()
    for helper_name, _, _ in helper_calls:
        helper_impl = "helper_" + helper_name[len("gen_helper_"):]
        if helper_owns_memory(helper_impl, helper_sources):
            referenced_owned.add(helper_name)
    missing_owned = sorted(referenced_owned - manifest_helper_names)
    for helper_name in missing_owned:
        errors.append(f"reachable memory helper {helper_name} is unclassified")

    # Function-pointer helper references are not calls in translate.c.  The
    # masked source keeps this scan independent of comments and strings, and
    # helper_body_has_class follows the generated helper body transitively.
    dispatch_pattern = re.compile(
        r"\b(gen_helper_[A-Za-z0-9_]+)\b(?!\s*\()")
    for match in dispatch_pattern.finditer(masked_translate):
        helper_name = match.group(1)
        helper_impl = "helper_" + helper_name[len("gen_helper_"):]
        line_no = source_line(translate_text, match.start()) - 1
        if helper_owns_memory(helper_impl, helper_sources) and \
                helper_name not in manifest_helper_names:
            fail(errors, line_no,
                 f"dispatch helper {helper_name} owns guest memory but is not in manifest")
        if helper_name not in manifest_helper_names:
            continue
        helper_count += 1
        class_token = manifest_class.get(helper_name)
        if class_token and not helper_body_has_class(
                helper_impl, class_token, helper_sources):
            fail(errors, line_no,
                 f"dispatch helper {helper_name} body lacks manifest class {class_token}")

    # Every helper-body guest-memory primitive is either covered by the
    # explicit privilege-dependent file gate or belongs to a helper family
    # that has a manifest member and a corresponding semantic event.
    helper_body_count = 0
    for path, helper_text in helper_sources:
        body_calls = memory_body_calls(helper_text)
        helper_body_count += len(body_calls)
        if not body_calls:
            continue
        if path.name in manifest_file_tokens:
            continue
        owners = []
        for helper_name in manifest_helper_names:
            helper_impl = "helper_" + helper_name[len("gen_helper_"):]
            if helper_owns_memory(helper_impl, [(path, helper_text)]):
                owners.append(helper_name)
        if not owners:
            errors.append(
                f"{path.name}: guest-memory helper body has no manifest owner")

    # Class agreement for supported helper rows is checked against the exact
    # switch/function region containing each callsite.  The body check covers
    # generated/function-pointer helpers that publish from their own code.
    for helper_name, start, _end in helper_calls:
        if helper_name not in manifest_helper_names or \
                helper_name in unsupported_helper_names:
            continue
        class_token = manifest_class.get(helper_name)
        if class_token is None:
            continue
        helper_impl = "helper_" + helper_name[len("gen_helper_"):]
        if helper_body_has_class(helper_impl, class_token, helper_sources):
            continue
        span = enclosing_span(translate_spans, start)
        if span is None:
            continue
        region_start, region_end = region_for(start, span)
        region_events = events_in_region(region_start, region_end)
        if not any(class_token in translate_text[event[1]:event[2]]
                   for event in region_events):
            fail(errors, source_line(translate_text, start) - 1,
                 f"helper {helper_name} event lacks manifest class {class_token}")

    # Keep this gate meaningful if the translator is substantially rewritten:
    # an empty scan is never accepted as complete coverage.
    if direct_count < 20:
        errors.append(f"only {direct_count} direct guest-memory primitives found")

    if errors:
        print("semantic inventory: FAIL", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1

    print(
        f"PASS semantic inventory gate "
        f"({len(manifest_rows)} manifest families, "
        f"{direct_count} direct primitives, {atomic_count} atomic primitives, "
        f"{helper_count} classified helper callsites, "
        f"{helper_body_count} helper-body memory operations, "
        f"{literal_event_count} literal translator events, "
        f"{helper_event_count} helper publisher events, "
        f"{dynamic_event_count} dynamic producer events)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
