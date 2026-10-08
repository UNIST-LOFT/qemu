/* Runtime metadata fixture: labels independently distinguish canonical identity
 * from raw signal/model PCs. Exclusions remain active even with identity proof. */
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

int main(int argc, char **argv)
{
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
