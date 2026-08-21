/* t14: EA static: malloc via the traced PLT stub.  Allocating through
 * the stub, then freeing through it, must be handled with no finding. */
#include <stdlib.h>

int main(void) {
    char *p = malloc(16);
    free(p);
    return 0;
}
