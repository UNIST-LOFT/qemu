/* t82: one unusable mutation attempt must not end the sweep.
 *
 * The guard variable is uninitialized on purpose.  The mutation planner turns
 * each observed read into a generic mutation plan, so one of those plans
 * rewrites `guard` and diverts control before the patch site.  That attempt
 * reaches no patch-site branch: it is an ordinary no-observation miss which
 * must be discarded and followed by the next plan.  The later plans keep the
 * child on the original path and still publish a heap-buffer-overflow, so the
 * tracer must report more than one attempt and a non-continue stop reason
 * while the deferred finding stays observable throughout.
 */
#include <stdlib.h>

int main(void) {
    char *p = malloc(8);
    int guard;
    if (p == NULL) return 0;
    if (guard == 0x5A5A) return 1; /* never true for the baseline value */
    p[9] = 1;                      /* heap-buffer-overflow */
    free(p);
    return 0;
}
