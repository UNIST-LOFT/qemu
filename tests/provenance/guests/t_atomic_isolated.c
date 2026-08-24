#include <stdint.h>
#include <stdlib.h>
/* Put the atomic op in a separate function to force a TB boundary.
 * The caller writes the initial value, calls the atomic function,
 * then reads the result — each in a different TB. */
static volatile uintptr_t slot;
__attribute__((noinline))
static void do_atomic(void) {
    __asm__ volatile (
        "lock xorq $1, %0\n\t"
        "lock xorq $1, %0"
        : "+m" (slot)
        :
        : "cc", "memory");
}
int main(void) {
    slot = UINT64_C(0x123456789abcdef0);
    do_atomic();
    return (int)(slot != UINT64_C(0x123456789abcdef0) ? 21 : 0);
}
