/* t36: a load whose destination overwrites its own EA base register
 * (mov 8(%rax), %rax) must still be checked against the pre-load base
 * value and tag (§6: snapshot the pre-access base; the post-access check
 * must not observe the loaded value).  The OOB load must be reported. */
#include <stdlib.h>

int main(void) {
    char *p = malloc(8);
    if (!p) return 0;
    __asm__ volatile("mov 8(%0), %0" : "+r"(p) : : "memory");
    return 0;
}
