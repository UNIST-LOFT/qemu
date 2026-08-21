/* t07: far OOB: access far past the allocation must be reported as OOB
 * against the tracked object. */
#include <stdlib.h>

int main(void) {
    char *p = malloc(8);
    p[1000] = 1;
    return 0;
}
