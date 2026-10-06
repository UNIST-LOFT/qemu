#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv)
{
    if (argc != 2) return 2;
    int kind = atoi(argv[1]);
    size_t size = kind <= 1 ? 8 : 1;
    char *left = malloc(size), *right = malloc(size);
    if (!left || !right) return 3;
    memset(left, 'A', size);
    memset(right, 'B', size);
    volatile size_t result;
    switch (kind) {
    case 0: result = strlen(left); break;
    case 1: result = strnlen(left, size + 1); break;
    case 2:
        left[0] = 0;
        result = strnlen(left, 64);
        if (result != 0) return 4;
        break;
    case 3:
        result = memchr(left, 'A', 64) == left;
        if (result != 1) return 5;
        break;
    case 4:
        result = memcmp(left, right, 64) != 0;
        if (result != 1) return 6;
        break;
    case 5:
        result = strncmp(left, right, 64) != 0;
        if (result != 1) return 7;
        break;
    default: return 8;
    }
    free(left);
    free(right);
    return 0;
}
