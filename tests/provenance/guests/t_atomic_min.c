#include <stdint.h>
/* Global variable — no stack load needed before the atomic op */
static volatile uintptr_t slot = UINT64_C(0x123456789abcdef0);
int main(void) {
    __asm__ volatile (
        "lock xorq $1, %0\n\t"
        "lock xorq $1, %0"
        : "+m" (slot)
        :
        : "cc", "memory");
    return (int)(slot != UINT64_C(0x123456789abcdef0) ? 21 : 0);
}
