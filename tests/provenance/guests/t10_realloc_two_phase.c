/* t10: two-phase realloc: the old pointer must remain valid until the
 * realloc returns.  Failed realloc (huge size) keeps the old object live
 * and the old pointer usable. */
#include <stdint.h>
#include <stdlib.h>

int main(void) {
    char *p = malloc(64);
    if (!p) return 0;
    /* Overflowing size → glibc returns NULL without touching p. */
    char *q = realloc(p, SIZE_MAX / 2 + 1);
    if (q) {
        q[0] = 1;
        free(q);
        return 0;
    }
    /* Failed realloc: p must still be usable. */
    p[0] = 1;
    free(p);
    return 0;
}
