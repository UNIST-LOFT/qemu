/* t05: out-of-bounds: 1 byte past the end (offset == size). */
#include <stdlib.h>

int main(void) {
    char *p = malloc(8);
    p[8] = 1;
    return 0;
}
