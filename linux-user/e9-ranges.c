#include "e9-ranges.h"

#include <stdlib.h>
#include <string.h>

/* Consume hex explicitly: strtoull also accepts signs and whitespace. */
static int parse_hex(const char **cursor, uintptr_t bias, uintptr_t *result)
{
    const char *p = *cursor;
    uint64_t value = 0;
    if (p[0] == '0' && (p[1] == 'x' || p[1] == 'X')) p += 2;
    const char *start = p;
    for (;;) {
        unsigned digit;
        if (*p >= '0' && *p <= '9') digit = *p - '0';
        else if (*p >= 'a' && *p <= 'f') digit = *p - 'a' + 10;
        else if (*p >= 'A' && *p <= 'F') digit = *p - 'A' + 10;
        else break;
        if (value > (UINT64_MAX - digit) / 16) return -1;
        value = value * 16 + digit;
        p++;
    }
    if (p == start || value > UINTPTR_MAX - bias) return -1;
    *cursor = p;
    *result = (uintptr_t)value + bias;
    return 0;
}

static int record_count(const char *value, size_t width, size_t *count)
{
    *count = 0;
    if (value == NULL || *value == '\0') return 0;
    *count = 1;
    for (const char *p = value; *p; p++) {
        if (*p == ',') {
            if (*count == SIZE_MAX / width) return -1;
            (*count)++;
        }
    }
    return 0;
}

int e9_parse_exclude_ranges(const char *value, uintptr_t load_bias,
                            e9_exclude_region **regions, size_t *len,
                            size_t *cap)
{
    size_t count;
    if (record_count(value, sizeof(**regions), &count) != 0) return -1;
    e9_exclude_region *parsed = count ? malloc(count * sizeof(*parsed)) : NULL;
    if (count && parsed == NULL) return -1;
    const char *p = value;
    for (size_t i = 0; i < count; i++) {
        if (p[0] != '0' || (p[1] != 'x' && p[1] != 'X') ||
            parse_hex(&p, load_bias, &parsed[i].start) != 0 || *p++ != '-' ||
            p[0] != '0' || (p[1] != 'x' && p[1] != 'X') ||
            parse_hex(&p, load_bias, &parsed[i].end) != 0 ||
            parsed[i].start >= parsed[i].end ||
            *p != (i + 1 == count ? '\0' : ',')) {
            free(parsed);
            return -1;
        }
        if (i + 1 < count) p++;
    }
    free(*regions);
    *regions = parsed;
    *len = *cap = count;
    return 0;
}

bool e9_is_in_exclude_region(const e9_exclude_region *regions, size_t len,
                             uintptr_t pc)
{
    for (size_t i = 0; i < len; i++) {
        if (pc >= regions[i].start && pc < regions[i].end) return true;
    }
    return false;
}

int e9_parse_relocated_instructions(const char *value, uintptr_t load_bias,
                                    const e9_exclude_region *regions,
                                    size_t regions_len,
                                    e9_relocated_instruction **instructions,
                                    size_t *len)
{
    size_t count;
    if (record_count(value, sizeof(**instructions), &count) != 0) return -1;
    e9_relocated_instruction *parsed = count ? malloc(count * sizeof(*parsed)) : NULL;
    if (count && parsed == NULL) return -1;
    const char *p = value;
    for (size_t i = 0; i < count; i++) {
        if (parse_hex(&p, load_bias, &parsed[i].relocated) != 0 || *p++ != ':' ||
            parse_hex(&p, load_bias, &parsed[i].original) != 0 ||
            *p != (i + 1 == count ? '\0' : ',') ||
            (i && parsed[i - 1].relocated >= parsed[i].relocated) ||
            !e9_is_in_exclude_region(regions, regions_len, parsed[i].relocated) ||
            e9_is_in_exclude_region(regions, regions_len, parsed[i].original)) {
            free(parsed);
            return -1;
        }
        if (i + 1 < count) p++;
    }
    free(*instructions);
    *instructions = parsed;
    *len = count;
    return 0;
}

bool e9_lookup_original_instruction(const e9_relocated_instruction *instructions,
                                    size_t len, uintptr_t pc,
                                    uintptr_t *original)
{
    size_t low = 0, high = len;
    while (low < high) {
        size_t middle = low + (high - low) / 2;
        if (pc < instructions[middle].relocated) high = middle;
        else if (pc > instructions[middle].relocated) low = middle + 1;
        else {
            *original = instructions[middle].original;
            return true;
        }
    }
    return false;
}
