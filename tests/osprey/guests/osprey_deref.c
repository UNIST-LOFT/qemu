/* osprey_deref: OSPREY structural-type fixture.
 *
 * Two heap allocations; the first block is dereferenced at +8 (a field
 * access through a stack pointer), a byte is copied from the first
 * block to the second, then both are freed.  Exercises F01 (malloc),
 * F02 (points-to through the return-value origin), F03 (copy), and the
 * pointer-candidate decode + consumer path. */
#include <stdlib.h>

int main(void) {
    char *p = malloc(32);
    if (!p) return 0;
    char *q = malloc(16);
    if (!q) return 0;
    p[8] = 1;              /* deref through the heap pointer */
    q[0] = p[8];           /* heap-to-heap byte copy */
    free(p);
    free(q);
    return 0;
}
