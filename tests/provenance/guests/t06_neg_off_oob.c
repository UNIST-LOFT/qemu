/* t06: negative-offset OOB: 1 byte before the object. */
#include <stdlib.h>

int main(void) {
    char *p = malloc(8);
    p[-1] = 1;
    return 0;
}
