/* Symbolic execution must retain a branch query created after a finding. */
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>

int main(void) {
    const char *path = getenv("SYMBOLIC_TESTCASE_NAME");
    char input = 0;
    if (!path) return 90;
    int fd = open(path, O_RDONLY);
    if (fd < 0 || read(fd, &input, 1) != 1) return 91;
    close(fd);

    char *p = malloc(8);
    if (!p) return 92;
    p[9] = 1;
    if (input == 'Z') {
        p[0] = 2;
    }
    free(p);
    return 0;
}
