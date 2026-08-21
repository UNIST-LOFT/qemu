#!/usr/bin/env python3
"""Generate the PLT_INFO_FILE (CSV) for a dynamically linked guest binary.

The tracer's provenance engine resolves malloc/calloc/realloc/free and the
libc string/memory models through the guest's PLT stubs: `parse_plt_info`
(tcg/symbolic/symbolic.c) parses each line as `image,name,0xoffset`, and
`load_image` (elfload.c) registers `symbolic_start_code + offset` as the
dispatch PC for `is_symbolic_model`. The offset must therefore be relative
to the guest's first executable LOAD segment (== symbolic_start_code), and
the address must be the *PLT stub* address, NOT the GOT/JUMP_SLOT address
(the guest executes the stub, and the dispatch lookup uses the executed PC).

This script replicates fuzzolic/find_models_addrs.py `process_plt` exactly:

  base = first address of `objdump -d` output (the binary's lowest text
         address; for `-no-pie` guests this is the first R E LOAD segment)
  stub = address of each `name@plt` label in `objdump -d`
  row  = f"{basename},{name},0x{stub - base:x}"

Only names handled by the tracer's model chain are emitted (the union of
MODELS and MODELS_LIBC below, which matches the elif chain in
parse_plt_info).  Unknown models are freed by the tracer, so emitting extra
names would be harmless but pointless.

Output format (one CSV line per import):
    probe_guest,free,0x60
"""

import argparse
import os
import subprocess

# Names recognized by the tracer's parse_plt_info chain.
MODELS_LIBC = ["malloc", "free", "realloc", "calloc", "printf", "fprintf",
               "vfprintf", "fputc", "_IO_printf"]
MODELS = [
    "strcmp",      # indirect call, offset in libc.so is not useful
    "strncmp",     # indirect call
    "strlen",      # indirect call
    "strnlen",     # indirect call
    "memchr",      # indirect call
    "memcmp",      # indirect call
    "memmove",     # indirect call
    "__printf_chk",
    "__memmove_chk",
    "memset",
    "__memset_chk",
    "memcpy",
    "__memcpy_chk",
    "strcpy",
    "strncpy",
    "atoi",
    "atol",
    "atoll",
    "strtol",
    "strtoul",
    "strtoll",
    "strtoull",
]


def process_plt(binary, outfile=None):
    """Write `basename,name,0xoffset` rows for every modeled PLT stub."""
    base_out = subprocess.check_output(
        ["objdump", "-d", binary], text=True)
    base_address = None
    for line in base_out.splitlines():
        if "0000" in line:
            base_address = int(line.split(" ")[0], 16)
            break
    if base_address is None:
        raise SystemExit(f"gen_plt: cannot determine base address of {binary}")

    try:
        res = subprocess.check_output(
            ["objdump", "-d", binary], text=True)
    except subprocess.CalledProcessError:
        res = ""
    for el in res.splitlines():
        if "@plt>:" not in el:
            continue
        split = el.split(" ")
        addr = int(split[0], 16) - base_address
        name = split[1][1:split[1].find("@")]
        if name in MODELS or name in MODELS_LIBC:
            line = f"{os.path.basename(binary)},{name},0x{addr:x}\n"
            if outfile is None:
                print(line, end="")
            else:
                outfile.write(line)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-o", "--output", help="output path (default: stdout)")
    ap.add_argument("binary", metavar="<binary>", help="path to the guest binary")
    args = ap.parse_args()

    if args.output:
        with open(args.output, "w") as outfile:
            process_plt(args.binary, outfile)
    else:
        process_plt(args.binary, None)


if __name__ == "__main__":
    main()
