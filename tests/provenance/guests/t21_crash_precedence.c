/* t21: crash precedence: a real target signal must win the verdict over
 * a deferred provenance finding.  First record an OOB finding (p[9],
 * mapped heap page, deferred), then cause a real SIGSEGV (p[1MB], beyond
 * the mapping) which terminates qemu with 128+SIGSEGV = 139.  The exit
 * record keeps "unhandled_target_signal" (real crash wins). */
#include <stdlib.h>

int main(void) {
    char *p = malloc(8);
    if (!p) return 0;
    p[9] = 1;           /* OOB: finding recorded, execution continues */
    p[1000000] = 1;     /* real SIGSEGV: wins the verdict */
    return 0;
}
