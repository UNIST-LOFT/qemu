/* t34: a failed malloc must create no object and must not corrupt
 * subsequent allocations (§3: on allocation failure, create no object
 * and invalidate the ABI return-register tag). */
#include <stdint.h>
#include <stdlib.h>

int main(void) {
    char *p = malloc(SIZE_MAX / 2);
    if (p) return 0; /* must fail */
    char *q = malloc(16);
    if (!q) return 0;
    q[0] = 1;
    free(q);
    return 0;
}
