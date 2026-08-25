/* A successful modeled strcpy must check the full destination write and use
 * RSI, not the destination register, for source-string provenance. */
#include <stdlib.h>
#include <string.h>

int main(void)
{
    char *dst = malloc(8);
    if (!dst) {
        return 100;
    }
    strcpy(dst, "0123456789abcdef");
    return 0;
}
