/* t08_bound_reject: explicit x86-64 fail-closed gate for legacy BOUND.
 *
 * Long mode treats opcode 0x62 as an EVEX prefix, so a 32-bit BOUND form
 * cannot be a positive x86-64 F01 fixture.  The translator must reject the
 * attempted legacy producer before the illegal-op exit rather than silently
 * accepting a sample that omitted its bounds read.
 */
#include <setjmp.h>
#include <signal.h>
#include <stddef.h>

static sigjmp_buf fault_jmp;
static volatile sig_atomic_t fault_seen;

static void fault_handler(int sig)
{
    fault_seen = sig;
    siglongjmp(fault_jmp, 1);
}

int main(void)
{
    struct sigaction sa;
    struct sigaction old_ill;
    struct sigaction old_segv;
    unsigned int bounds[2] = {0, 0xffffffffu};

    sa.sa_handler = fault_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;
    if (sigaction(SIGILL, &sa, &old_ill) != 0 ||
        sigaction(SIGSEGV, &sa, &old_segv) != 0) {
        return 1;
    }

    fault_seen = 0;
    if (sigsetjmp(fault_jmp, 1) == 0) {
        __asm__ volatile(
            ".globl t08_bound32\n"
            "t08_bound32:\n"
            ".byte 0x62, 0x00\n"
            : : "a"(bounds) : "cc", "memory");
    }

    if (sigaction(SIGILL, &old_ill, NULL) != 0 ||
        sigaction(SIGSEGV, &old_segv, NULL) != 0) {
        return 1;
    }
    return fault_seen == 0;
}
