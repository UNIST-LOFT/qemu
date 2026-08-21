/* t20: symbolic continuation: a provenance finding detected mid-run must
 * NOT terminate the guest; execution continues and the finding is
 * finalized as a synthetic crash at normal exit (guest exit code 0).
 * Runs in symbolic mode (solver attached). */
#include <stdlib.h>

int main(void) {
    volatile char *p = malloc(8);
    if (!p) return 0;
    p[1000] = 1;   /* OOB: finding deferred, execution continues */
    free((void *)p);
    return 0;
}
