/* One injected byte must survive moving, same-address, shrinking and failed
 * realloc. The sole input-dependent branch checks the preserved payload;
 * loss of its expression removes the harness's required branch query. */
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

int main(int argc, char **argv)
{
    if (argc != 2) return 100;
    char warmup[2], source[2] = {'a', 'b'};
    memcpy(warmup, source, 2);
    if (warmup[1] != 'b') return 101;
    char *p = malloc(64);
    void *blocker = malloc(64);
    if (!p || !blocker) return 102;
    p[7] = 'A';
    const char *path = getenv("SYMBOLIC_TESTCASE_NAME");
    if (path) {
        int fd = open(path, O_RDONLY);
        if (fd < 0 || read(fd, p + 7, 1) != 1) return 103;
        close(fd);
    }
    uintptr_t before = (uintptr_t)p;
    char *q;
    if (argv[1][0] == 'm') {
        q = realloc(p, 65536);
        if (!q || (uintptr_t)q == before) return 104;
    } else if (argv[1][0] == 's') {
        q = realloc(p, 64);
        if (!q || (uintptr_t)q != before) return 105;
    } else if (argv[1][0] == 'h') {
        q = realloc(p, 16);
        if (!q) return 106;
    } else if (argv[1][0] == 'f') {
        q = realloc(p, SIZE_MAX / 2 + 1);
        if (q) return 107;
        q = p;
    } else {
        return 108;
    }
    volatile int result = 0;
    if (q[7] == 'Z') result = 1;
    fprintf(stderr, "realloc-payload mode=%c branch=%d\n", argv[1][0], result);
    free(q);
    free(blocker);
    return result;
}
