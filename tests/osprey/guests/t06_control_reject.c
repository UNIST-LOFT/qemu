/* t06_control_reject: fail-closed control/descriptor helper coverage.
 *
 * The translator recognizes these user-mode control paths but their helper
 * memory footprints depend on privilege, descriptor, or task-state data.
 * Each instruction is attempted under a signal guard: valid descriptor
 * queries may return, while far returns may raise the expected user-mode
 * fault.  The semantic unsupported boundary must reject the sample before a
 * helper fault can silently turn the path into an apparently complete F01
 * observation.
 */
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stddef.h>

static sigjmp_buf fault_jmp;
static volatile sig_atomic_t fault_seen;
static volatile uint64_t g_sink;

static void fault_handler(int sig)
{
    fault_seen = sig;
    siglongjmp(fault_jmp, 1);
}

static int attempt(void (*fn)(void))
{
    fault_seen = 0;
    if (sigsetjmp(fault_jmp, 1) == 0) {
        fn();
    }
    return fault_seen;
}

__attribute__((noinline, used)) static void descriptor_queries(void)
{
    uint16_t selector = 0;
    uint64_t value = 0;

    __asm__ volatile(
        ".globl t06_lar\n"
        "t06_lar:\n"
        "lar %1, %0\n"
        : "=r"(value) : "m"(selector) : "cc");
    __asm__ volatile(
        ".globl t06_lsl\n"
        "t06_lsl:\n"
        "lsl %1, %0\n"
        : "=r"(value) : "m"(selector) : "cc");
    __asm__ volatile(
        ".globl t06_verr\n"
        "t06_verr:\n"
        "verr %0\n"
        : : "m"(selector) : "cc");
    __asm__ volatile(
        ".globl t06_verw\n"
        "t06_verw:\n"
        "verw %0\n"
        : : "m"(selector) : "cc");
    g_sink ^= value;
}

__attribute__((naked, noinline, used)) static void far_return(void)
{
    __asm__ volatile(
        ".globl t06_lret\n"
        "t06_lret:\n"
        "lea 1f(%rip), %rax\n"
        "pushq $0x33\n"
        "pushq %rax\n"
        "lretq\n"
        "1:\n"
        "ret\n");
}

__attribute__((naked, noinline, used)) static void interrupt_return(void)
{
    __asm__ volatile(
        ".globl t06_iret\n"
        "t06_iret:\n"
        "lea 1f(%rip), %rax\n"
        "pushfq\n"
        "popq %rdx\n"
        "pushq %rdx\n"
        "pushq $0x33\n"
        "pushq %rax\n"
        "iretq\n"
        "1:\n"
        "ret\n");
}

int main(void)
{
    struct sigaction sa;
    struct sigaction old_segv;
    struct sigaction old_ill;
    struct sigaction old_bus;

    sa.sa_handler = fault_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;
    if (sigaction(SIGSEGV, &sa, &old_segv) != 0 ||
        sigaction(SIGILL, &sa, &old_ill) != 0 ||
        sigaction(SIGBUS, &sa, &old_bus) != 0) {
        return 1;
    }

    (void)attempt(descriptor_queries);
    (void)attempt(far_return);
    (void)attempt(interrupt_return);
    g_sink ^= (uint64_t)fault_seen;

    if (sigaction(SIGSEGV, &old_segv, NULL) != 0 ||
        sigaction(SIGILL, &old_ill, NULL) != 0 ||
        sigaction(SIGBUS, &old_bus, NULL) != 0) {
        return 1;
    }
    return 0;
}
