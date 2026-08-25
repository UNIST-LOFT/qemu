/* strncpy writes exactly n bytes, including zero padding after an early NUL.
 * The modeled destination interval must therefore be n, not strlen(src)+1. */
#include <stdlib.h>
#include <string.h>

int main(void)
{
    char *dst = malloc(8);
    if (!dst) {
        return 101;
    }
    strncpy(dst, "x", 16);
    return 0;
}
