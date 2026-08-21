/* t02: double-free of a small allocation must be a no-op. */
#include <stdlib.h>

int main(void) {
    char *p = malloc(4);
    free(p);
    free(p);
    return 0;
}
