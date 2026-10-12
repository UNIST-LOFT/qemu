/* Runtime metadata fixture: labels independently distinguish canonical identity
 * from raw signal/model PCs. Exact originals may be checked inside exclusions;
 * unmapped E9 helper instructions remain excluded. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

__asm__(".text\n"
        ".global e9_original_signal\n"
        "e9_original_signal: movb $1,(%rax)\n ret\n"
        ".global e9_raw_signal\n"
        "e9_raw_signal: movb $1,(%rax)\n ret\n"
        ".global e9_original_model\n"
        "e9_original_model: nop\n ret\n");
extern void e9_raw_signal(void);

/* The anchors are never executed and have exactly the relocated instruction's
 * bytes. The aligned mixed block fits within one page and has no branch before
 * its return, so helpers and originals share one straight-line TB. All five
 * memory accesses use the same live, fully initialized 40-byte allocation. */
__asm__(".text\n"
        ".global e9_clean_original_load\n"
        "e9_clean_original_load: movq (%rdi),%rax\n ret\n"
        ".global e9_clean_original_store\n"
        "e9_clean_original_store: movq %rax,24(%rdi)\n ret\n"
        ".p2align 6\n"
        ".global e9_clean_block_begin\n"
        ".global e9_clean_helper_before\n"
        "e9_clean_block_begin:\n"
        "e9_clean_helper_before: movq 8(%rdi),%rcx\n"
        ".global e9_clean_raw_load\n"
        "e9_clean_raw_load: movq (%rdi),%rax\n"
        ".global e9_clean_helper_between\n"
        "e9_clean_helper_between: movq %rcx,16(%rdi)\n"
        ".global e9_clean_raw_store\n"
        "e9_clean_raw_store: movq %rax,24(%rdi)\n"
        ".global e9_clean_helper_after\n"
        "e9_clean_helper_after: movq %rcx,32(%rdi)\n"
        ".global e9_clean_return\n"
        "e9_clean_return: ret\n"
        ".global e9_clean_block_end\n"
        "e9_clean_block_end:\n");
extern uint64_t e9_clean_block_begin(uint64_t *payload);

static int clean_control(void)
{
    const uint64_t original = UINT64_C(0x123456789abcdef0);
    const uint64_t helper = UINT64_C(0x0fedcba987654321);
    uint64_t *payload = malloc(5 * sizeof(*payload));
    if (!payload) return 2;
    payload[0] = original;
    payload[1] = helper;
    payload[2] = 0;
    payload[3] = 0;
    payload[4] = 0;
    uint64_t result = e9_clean_block_begin(payload);
    int valid = result == original && payload[0] == original &&
                payload[1] == helper && payload[2] == helper &&
                payload[3] == original && payload[4] == helper;
    if (valid) {
        fprintf(stderr, "e9-clean-control value=%016" PRIx64
                " stored=%016" PRIx64 " helper=%016" PRIx64
                " preserved=5\n", result, payload[3], payload[4]);
    }
    free(payload);
    return valid ? 0 : 3;
}

int main(int argc, char **argv)
{
    if (argc > 1 && strcmp(argv[1], "clean") == 0) {
        return clean_control();
    }
    if (argc > 1 && strcmp(argv[1], "signal") == 0) {
        __asm__ volatile("xor %%eax,%%eax\n call e9_raw_signal" ::: "rax", "memory");
    } else {
        char *p = malloc(8);
        if (!p) return 0;
        memcpy(p, "0123456789abcdef", 16);
        __asm__ volatile(".global e9_raw_model\n e9_raw_model: nop" ::: "memory");
        if (argc > 1 && strcmp(argv[1], "precedence") == 0) {
            __asm__ volatile("xor %%eax,%%eax\n call e9_raw_signal" ::: "rax", "memory");
        }
        if (argc > 1 && strcmp(argv[1], "timeout") == 0) {
            for (;;) __asm__ volatile("" ::: "memory");
        }
    }
    return 0;
}
