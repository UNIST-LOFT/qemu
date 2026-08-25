/* strcmp may compare strings with different allocation lengths. The shorter
 * string is read only through its NUL, not through the longer string's size. */
#include <stdlib.h>
#include <string.h>

int main(void)
{
    char *short_string = malloc(2);
    if (!short_string) {
        return 115;
    }
    short_string[0] = 'A';
    short_string[1] = '\0';
    volatile int result = strcmp(short_string, "ABCD");
    (void)result;
    free(short_string);
    return 0;
}
