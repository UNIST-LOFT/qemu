/* t28: UNKNOWN provenance must NOT report UAF from numeric address
 * history.  A 32-bit write preserves the pointer value but kills the tag;
 * accessing the freed address afterwards must produce no finding (§7:
 * provenance identity, not address history, is required for UAF). */
#include <stdint.h>
#include <stdlib.h>

int main(void) {
    char *p = malloc(16);
    if (!p) return 0;
    free(p);
    uintptr_t a = (uintptr_t)p;
    /* 32-bit write: value preserved (heap addresses are < 4 GiB), tag
     * must be invalidated by the partial-register write. */
    __asm__ volatile("mov %k0, %k0" : "+r"(a) : : );
    char *q = (char *)a;
    q[0] = 1; /* UNKNOWN: must NOT be UAF */
    return 0;
}
