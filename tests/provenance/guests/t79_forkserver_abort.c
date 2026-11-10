/* A deferred UAF followed by an infinite loop reaches the child deadline.
 * The parent preserves the provenance diagnostic but must reject this timed-out
 * BINRADAR baseline: no canonical evidence or replayable mutation source. */
#include <stdlib.h>

int main(void) {
    char *p = malloc(8);
    if (!p) return 0;
    free(p);
    for (;;) {
        p[0] = 1; /* UAF on every iteration; never returns */
    }
    return 0;
}