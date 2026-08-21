/* t04: classic heap use-after-free: write through a freed pointer. */
#include <stdlib.h>

int main(void) {
    char *p = malloc(64);
    free(p);
    p[0] = 1;
    return 0;
}
