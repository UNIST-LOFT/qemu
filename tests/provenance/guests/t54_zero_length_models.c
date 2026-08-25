/* Bounded zero-length libc operations do not access their pointer arguments.
 * Model preflight must not reinterpret strnlen/strncmp(..., 0) as unbounded. */
#include <stddef.h>
#include <string.h>

int main(void)
{
    const char *bad = (const char *)1;
    char *bad_dst = (char *)1;

    if (strnlen(bad, 0) != 0) {
        return 108;
    }
    if (strncmp(bad, bad, 0) != 0) {
        return 109;
    }
    if (memchr(bad, 'x', 0) != NULL) {
        return 110;
    }
    if (memcmp(bad, bad, 0) != 0) {
        return 111;
    }
    if (memcpy(bad_dst, bad, 0) != bad_dst) {
        return 112;
    }
    if (memset(bad_dst, 0, 0) != bad_dst) {
        return 113;
    }
    if (strncpy(bad_dst, bad, 0) != bad_dst) {
        return 114;
    }
    return 0;
}
