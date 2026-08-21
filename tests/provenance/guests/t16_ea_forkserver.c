/* t16: forkserver mode: one allocation+free cycle inside the forkserver
 * child. Run with a forkserver driver; the child's findings are reported
 * through the shared trace data.  No bug here: expect a normal result. */
#include <stdlib.h>

int main(void) {
    char *p = malloc(32);
    if (!p) return 0;
    free(p);
    return 0;
}
