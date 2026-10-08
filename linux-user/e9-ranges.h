#ifndef BINRADAR_E9_RANGES_H
#define BINRADAR_E9_RANGES_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* Exact E9 exclusion intervals (loader + RESERVE + TRAMPOLINE maps of the
 * executing artifact), parsed from E9_EXCLUDE_RANGES.  Half-open
 * [start, end).  This module is plain C (no glib, no QEMU) so the parser
 * and membership checks are unit-testable without the tracer. */

typedef struct e9_exclude_region {
    uintptr_t start;
    uintptr_t end;
} e9_exclude_region;

/* Parse a canonical comma-separated interval list, atomically replacing
 * caller-owned storage. Missing or empty input yields 0 intervals. On
 * failure all outputs and existing storage are untouched. The input is
 * never modified.
 *
 * Grammar per token: 0x<hex>-0x<hex> with no trailing data, start < end,
 * and checked load_bias addition (overflow is malformed). */
int e9_parse_exclude_ranges(const char *value, uintptr_t load_bias,
                            e9_exclude_region **regions, size_t *len,
                            size_t *cap);

/* Half-open membership: true iff start <= pc < end for some interval. */
bool e9_is_in_exclude_region(const e9_exclude_region *regions, size_t len,
                             uintptr_t pc);

typedef struct e9_relocated_instruction {
    uintptr_t relocated;
    uintptr_t original;
} e9_relocated_instruction;

/* Strict sorted raw:original hex pairs, with checked bias on both PCs.
 * Raw PCs must lie in the selected exclusions, originals outside them.
 * Duplicate/unsorted entries and empty tokens fail atomically. Empty input
 * clears the map. Successful storage is immutable until reinitialization. */
int e9_parse_relocated_instructions(const char *value, uintptr_t load_bias,
                                    const e9_exclude_region *regions,
                                    size_t regions_len,
                                    e9_relocated_instruction **instructions,
                                    size_t *len);
bool e9_lookup_original_instruction(const e9_relocated_instruction *instructions,
                                    size_t len, uintptr_t pc,
                                    uintptr_t *original);

#endif /* BINRADAR_E9_RANGES_H */
