/* t31: an integer overwrite of a formerly tagged register must clear the
 * tag.  imul $1 preserves the value but is not pointer-preserving; the
 * freed-address access afterwards must not be UAF (§4: full-register
 * integer overwrite → UNKNOWN). */
#include <stdint.h>
#include <stdlib.h>

int main(void) {
    char *p = malloc(16);
    if (!p) return 0;
    free(p);
    uintptr_t a = (uintptr_t)p;
    __asm__ volatile("imul $1, %0" : "+r"(a) : : );
    char *q = (char *)a;
    q[0] = 1; /* UNKNOWN: must NOT be UAF */
    return 0;
}
