/* Memory CMP leaves its loaded value in a temporary until the semantic
 * event, unlike MOV-to-GPR.  It exercises the conservative fusion proof.
 * Reuse the exact instruction while changing object lifetime; the raw-only
 * SIMD load and genuine fault must retain their original checking paths. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

__attribute__((noinline)) static void compare(char *p)
{
    __asm__ volatile(
        ".globl raw_first_compare_pc\n"
        "raw_first_compare_pc:\n"
        "cmpq $0, 8(%0)\n"
        : : "r"(p) : "cc", "memory");
}

int main(int argc, char **argv)
{
    if (argc != 2) return 20;
    if (!strcmp(argv[1], "fault")) {
        compare(NULL);
        return 21;
    }
    if (!strcmp(argv[1], "raw")) {
        char *p = malloc(12);
        if (!p) return 22;
        __asm__ volatile(
            ".globl raw_only_compare_pc\n"
            "raw_only_compare_pc:\n"
            "movq 8(%0), %%xmm0\n"
            : : "r"(p) : "xmm0", "memory");
        puts("raw-only compare completed");
        return 0;
    }
    char *p = malloc(16);
    if (!p) return 23;
    compare(p);
    free(p);
    compare(p);
    puts("same-PC compare completed");
    return 0;
}
