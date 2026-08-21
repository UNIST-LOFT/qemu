/* t15: EA dynamic: the allocator is reached via a function pointer
 * (indirect call through a register). */
#include <stdlib.h>

int main(void) {
    void *(*fn)(size_t) = malloc;
    void *p = fn(16);
    if (!p) return 0;
    ((volatile char *)p)[0] = 1;
    free(p);
    return 0;
}
