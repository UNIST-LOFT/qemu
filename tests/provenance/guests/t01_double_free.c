/* t01: double free of a heap object must be a no-op (no finding). */
#include <stdlib.h>

int main(void) {
    char *p = malloc(16);
    free(p);
    free(p);
    return 0;
}
