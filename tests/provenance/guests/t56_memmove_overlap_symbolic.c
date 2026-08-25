/* Overlapping symbolic memmove toward a lower address must preserve source
 * expressions across the symbolic-memory 64-KiB leaf boundary. */
#include <fcntl.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

int main(void)
{
    const char *path = getenv("SYMBOLIC_TESTCASE_NAME");
    char *raw = malloc(0x20010);
    if (!path || !raw) {
        return 116;
    }

    uintptr_t boundary = ((uintptr_t)raw + 0x10000) & ~(uintptr_t)0xffff;
    char *src = (char *)boundary - 1;
    char *dst = src - 1;
    src[0] = 'B';
    src[2] = 'C';
    src[3] = 'D';

    int fd = open(path, O_RDONLY);
    if (fd < 0 || read(fd, src + 1, 1) != 1) {
        return 117;
    }
    close(fd);

    memmove(dst, src, 4);
    volatile int result = 0;
    if (dst[1] == 'Z') {
        result = 1;
    }
    free(raw);
    return result;
}
