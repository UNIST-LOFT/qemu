/* t26: use-after-free via a *generated* pointer: the freed address is
 * obtained through a helper (pointer arithmetic after free), not stored
 * in a register across the free.  The provenance engine must still
 * identify the region by address. */
#include <stdint.h>
#include <stdlib.h>

int main(void) {
    char *p = malloc(16);
    if (!p) return 0;
    uintptr_t a = (uintptr_t)p;
    free(p);
    char *q = (char *)a; /* regenerate the address after free */
    q[0] = 1;            /* UAF through regenerated pointer */
    return 0;
}
