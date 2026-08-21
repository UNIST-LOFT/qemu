/* t13: memset model: filling past the object end must be reported OOB. */
#include <stdlib.h>
#include <string.h>

int main(void) {
    char *p = malloc(8);
    if (!p) return 0;
    memset(p, 0, 16); /* 16 > 8 → OOB */
    free(p);
    return 0;
}
