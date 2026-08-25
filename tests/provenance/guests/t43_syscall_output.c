/* A successful read overwriting a pointer slot must clear its stale tag. */
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>

int main(void) {
    int fds[2];
    char *p = malloc(16);
    if (!p || pipe(fds) != 0) return 70;
    void *slot = p;
    uintptr_t raw = (uintptr_t)p;
    if (write(fds[1], &raw, sizeof(raw)) != (ssize_t)sizeof(raw)) return 71;
    free(p);
    if (read(fds[0], &slot, sizeof(slot)) != (ssize_t)sizeof(slot)) return 72;
    volatile char value = ((char *)slot)[0];
    (void)value;
    return 0;
}
