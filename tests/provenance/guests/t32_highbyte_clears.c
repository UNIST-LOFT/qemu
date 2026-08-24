/* t32: a high-byte (AH) write must invalidate the architectural full
 * register (RAX), not a different shadow slot.  movb %ah, %ah preserves
 * the value; the freed-address access afterwards must not be UAF (§4:
 * partial-register write → tag(full_register) = UNKNOWN). */
#include <stdint.h>
#include <stdlib.h>

int main(void) {
    char *p = malloc(16);
    if (!p) return 0;
    free(p);
    uintptr_t a = (uintptr_t)p;
    __asm__ volatile("movb %h0, %h0" : "+a"(a) : : );
    char *q = (char *)a;
    q[0] = 1; /* UNKNOWN: must NOT be UAF */
    return 0;
}
