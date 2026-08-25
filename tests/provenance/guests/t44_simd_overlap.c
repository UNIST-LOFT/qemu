/* A SIMD store of identical pointer bytes must still invalidate the old tag. */
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>

int main(void) {
    int fds[2];
    char *p = malloc(16);
    if (!p || pipe(fds) != 0) return 80;
    void *slot __attribute__((aligned(16))) = p;
    uintptr_t raw = (uintptr_t)p;
    uintptr_t untagged = 0;
    if (write(fds[1], &raw, sizeof(raw)) != (ssize_t)sizeof(raw)) return 81;
    if (read(fds[0], &untagged, sizeof(untagged)) != (ssize_t)sizeof(untagged)) return 82;
    free(p);
    __asm__ volatile("movq %1, %%xmm0; movq %%xmm0, %0"
                     : "=m"(slot) : "m"(untagged) : "xmm0", "memory");
    volatile char value = ((char *)slot)[0];
    (void)value;
    return 0;
}
