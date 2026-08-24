/* t29: push/pop through the stack memory shadow must preserve the tag.
 * A freed pointer pushed and popped must still report UAF on use (§5:
 * push rax; pop rbx → rbx receives rax's tag through the shadow). */
#include <stdlib.h>

int main(void) {
    char *p = malloc(16);
    if (!p) return 0;
    free(p);
    char *q = p; /* mov: tag transfer */
    __asm__ volatile("push %0\n\tpop %0" : "+r"(q) : : "memory");
    q[0] = 1; /* UAF: tag must survive the stack round-trip */
    return 0;
}
