/* t08: malloc(0) is representable: non-NULL pointer with size 0.
 * A 1-byte write must be reported OOB. */
#include <stdlib.h>

int main(void) {
    char *p = malloc(0);
    if (p) {
        p[0] = 1;
    }
    return 0;
}
