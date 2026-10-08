/* Focused unit tests for the E9 exclude-range parser and membership
 * checks (tracer/linux-user/e9-ranges.c).
 *
 * Compile standalone:  gcc -I../../linux-user e9-ranges-test.c \
 *                           ../../linux-user/e9-ranges.c -o e9-ranges-test
 *
 * Prints "RESULT <name> <pass|fail>" per case; exits nonzero on any
 * failure.  Covers: empty/missing list, one interval, multiple separated
 * intervals, exact start included / exact end excluded, gaps not excluded,
 * nonzero load bias, malformed hex, missing delimiter, reversed/empty
 * interval, overflow, and repeated initialization.
 */

#include "e9-ranges.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures = 0;

static void check(const char *name, int cond) {
    printf("RESULT %s %s\n", name, cond ? "pass" : "fail");
    if (!cond) {
        failures++;
    }
}

static int parse_ok(const char *value, uintptr_t load_bias,
                    e9_exclude_region **regions, size_t *len, size_t *cap) {
    free(*regions);
    *len = 0;
    *cap = 0;
    *regions = NULL;
    return e9_parse_exclude_ranges(value, load_bias, regions, len, cap);
}

static void test_instruction_map(void) {
    e9_exclude_region regions[] = {{0x5000, 0x6000}};
    e9_relocated_instruction *map = NULL;
    size_t len = 0;
    uintptr_t original = 0xdead;
    check("map-empty", e9_parse_relocated_instructions(NULL, 0, regions, 1,
                                                       &map, &len) == 0 && len == 0);
    check("map-exact", e9_parse_relocated_instructions("5000:1000,5010:1004", 0,
                                                       regions, 1, &map, &len) == 0 && len == 2);
    check("map-first", e9_lookup_original_instruction(map, len, 0x5000, &original) && original == 0x1000);
    check("map-last", e9_lookup_original_instruction(map, len, 0x5010, &original) && original == 0x1004);
    original = 0xdead;
    check("map-helper-unavailable", !e9_lookup_original_instruction(map, len, 0x5001, &original) && original == 0xdead);
    const char *invalid[] = {
        "5000:1000,5000:1004", "5010:1000,5000:1004",
        "5000:1000,", ",5000:1000", "5000:1000,,5010:1004",
        "5000:", ":1000", "5000:1000junk", "5000:1000:1004",
        "-5000:1000", "+5000:1000", " 5000:1000", "5000: 1000",
        "5000:0x", "0x:1000", "5000:10000000000000000",
        "10000000000000000:1000", "6000:1000", "5000:5001"
    };
    for (size_t i = 0; i < sizeof(invalid) / sizeof(*invalid); i++) {
        e9_relocated_instruction *saved = map;
        check(invalid[i], e9_parse_relocated_instructions(invalid[i], 0, regions, 1,
                                                         &map, &len) != 0 &&
              map == saved && len == 2 && map[0].original == 0x1000);
    }
    e9_exclude_region biased[] = {{0x405000, 0x406000}};
    check("map-bias", e9_parse_relocated_instructions("0x5000:0x1000", 0x400000,
                                                      biased, 1, &map, &len) == 0 &&
          map[0].relocated == 0x405000 && map[0].original == 0x401000);
    check("map-bias-lookup", e9_lookup_original_instruction(map, len, 0x405000, &original) && original == 0x401000);
    check("map-bias-not-twice", !e9_lookup_original_instruction(map, len, 0x5000, &original));
    check("map-raw-bias-overflow", e9_parse_relocated_instructions("ffffffffffffffff:1000", 1,
                                                                  regions, 1, &map, &len) != 0);
    check("map-original-bias-overflow", e9_parse_relocated_instructions("5000:ffffffffffffffff", 1,
                                                                       regions, 1, &map, &len) != 0);
    check("map-needs-selected-exclusion", e9_parse_relocated_instructions("5000:1000", 0,
                                                                         NULL, 0, &map, &len) != 0);
    check("map-clear", e9_parse_relocated_instructions("", 0, regions, 1,
                                                       &map, &len) == 0 && map == NULL && len == 0);
}

int main(void) {
    test_instruction_map();
    e9_exclude_region *regions = NULL;
    size_t len = 0;
    size_t cap = 0;

    /* Missing and empty list: no exclusions, success. */
    check("empty-list", parse_ok("", 0, &regions, &len, &cap) == 0 && len == 0);
    check("null-list", parse_ok(NULL, 0, &regions, &len, &cap) == 0 && len == 0);

    /* One interval. */
    check("one-interval",
          parse_ok("0x1000-0x2000", 0, &regions, &len, &cap) == 0
          && len == 1 && regions[0].start == 0x1000
          && regions[0].end == 0x2000);

    /* Multiple separated intervals. */
    check("multiple-intervals",
          parse_ok("0x1000-0x2000,0x5000-0x6000,0x9000-0xa000",
                   0, &regions, &len, &cap) == 0
          && len == 3 && regions[1].start == 0x5000
          && regions[2].end == 0xa000);

    /* Membership: exact start included, exact end excluded, gap free. */
    check("start-included",
          e9_is_in_exclude_region(regions, len, 0x1000));
    check("end-excluded",
          !e9_is_in_exclude_region(regions, len, 0x2000));
    check("inside-included",
          e9_is_in_exclude_region(regions, len, 0x1fff));
    check("gap-not-excluded",
          !e9_is_in_exclude_region(regions, len, 0x3000));
    check("before-not-excluded",
          !e9_is_in_exclude_region(regions, len, 0xfff));
    check("after-not-excluded",
          !e9_is_in_exclude_region(regions, len, 0xa000));
    free(regions);
    regions = NULL;

    /* Nonzero load bias applied exactly once. */
    check("load-bias",
          parse_ok("0x1000-0x2000", 0x400000, &regions, &len, &cap) == 0
          && len == 1 && regions[0].start == 0x401000
          && regions[0].end == 0x402000);
    check("load-bias-membership",
          e9_is_in_exclude_region(regions, len, 0x401000)
          && !e9_is_in_exclude_region(regions, len, 0x1000));
    free(regions);
    regions = NULL;

    /* Malformed inputs must fail, never partially parse. */
    check("malformed-hex",
          parse_ok("0x1000-0xzz00", 0, &regions, &len, &cap) != 0 && len == 0);
    check("missing-delimiter",
          parse_ok("0x1000", 0, &regions, &len, &cap) != 0 && len == 0);
    check("reversed-interval",
          parse_ok("0x2000-0x1000", 0, &regions, &len, &cap) != 0 && len == 0);
    check("empty-interval",
          parse_ok("0x1000-0x1000", 0, &regions, &len, &cap) != 0 && len == 0);
    check("trailing-data",
          parse_ok("0x1000-0x2000junk", 0, &regions, &len, &cap) != 0
          && len == 0);
    check("missing-prefix",
          parse_ok("1000-0x2000", 0, &regions, &len, &cap) != 0 && len == 0);
    check("bad-second-prefix",
          parse_ok("0x1000-2000", 0, &regions, &len, &cap) != 0 && len == 0);
    check("overflow-bias",
          parse_ok("0xffffffffffffffff-0xffffffffffffffff",
                   (uintptr_t)1, &regions, &len, &cap) != 0 && len == 0);
    check("overflow-end",
          parse_ok("0x1000-0xffffffffffffffff",
                   (uintptr_t)1, &regions, &len, &cap) != 0 && len == 0);
    check("partial-never-observable",
          parse_ok("0x1000-0x2000,0xzz00-0x3000", 0, &regions, &len, &cap)
          != 0 && len == 0);

    check("range-no-empty-token", parse_ok("0x1000-0x2000,", 0,
                                           &regions, &len, &cap) != 0);
    check("range-no-sign", parse_ok("0x+1000-0x2000", 0,
                                    &regions, &len, &cap) != 0);
    check("range-valid-before-atomic-failure", parse_ok("0x1000-0x2000", 0,
                                                      &regions, &len, &cap) == 0);
    e9_exclude_region *saved = regions;
    check("range-failure-preserves-storage",
          e9_parse_exclude_ranges("0x5000-0x6000,broken", 0,
                                  &regions, &len, &cap) != 0 &&
          regions == saved && len == 1 && regions[0].start == 0x1000);

    /* Repeated initialization must not retain old intervals. */
    check("reinit",
          parse_ok("0x1000-0x2000", 0, &regions, &len, &cap) == 0
          && parse_ok("0x5000-0x6000", 0, &regions, &len, &cap) == 0
          && len == 1 && regions[0].start == 0x5000);
    free(regions);

    if (failures) {
        printf("FAILED %d case(s)\n", failures);
        return 1;
    }
    printf("ALL PASS\n");
    return 0;
}
