#include <stdint.h>
static volatile uintptr_t slot = 0;
int main(void) {
    __asm__ volatile ("lock xorq $1, %0" : "+m" (slot) :: "cc", "memory");
    /* slot should be 1 after single xor */
    return (int)(slot != 1 ? 21 : 0);
}
