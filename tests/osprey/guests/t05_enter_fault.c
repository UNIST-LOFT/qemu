/* t05_enter_fault: later-constituent ENTER fault regression.
 *
 * ENTER first stores the old frame pointer, then reads the caller's frame
 * chain.  The first chain word below the supplied frame pointer is readable;
 * the second is on a protected page.  The first stack store therefore
 * commits, a later read faults, and the translator's post-success replay is
 * unreachable.  RSP remains at its pre-ENTER value, so the fault cannot
 * extend the canonical stack bound.
 */
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <sys/mman.h>
#include <unistd.h>

static sigjmp_buf fault_jmp;
static volatile sig_atomic_t fault_seen;
static volatile uint64_t g_sink;

static void fault_handler(int sig)
{
    (void)sig;
    fault_seen = 1;
    siglongjmp(fault_jmp, 1);
}

__attribute__((naked, noinline, used))
static void enter_body(void)
{
    __asm__ volatile(
        ".globl t05_enter_fault\n"
        "t05_enter_fault:\n"
        "enter $0, $31\n"
        "leave\n"
        "ret\n");
}

/* Establish the custom stack before the instrumented call.  This gives the
 * ENTER callee a stack-frame identity whose entry SP is the custom stack,
 * rather than asking stack-origin tracking to model an arbitrary pivot in
 * the middle of an already-registered caller frame. */
__attribute__((naked, noinline, used))
static void enter_on_custom_stack(void *stack_top, void *frame_base)
{
    __asm__ volatile(
        "mov %rsp, %r11\n"
        "mov %rbp, %r10\n"
        "mov %rdi, %rsp\n"
        "mov %rsi, %rbp\n"
        "call enter_body\n"
        "mov %r11, %rsp\n"
        "mov %r10, %rbp\n"
        "ret\n");
}

static int run_fault(void)
{
    struct sigaction sa;
    struct sigaction old_sa;
    uint8_t *map_region;
    uint8_t *stack_region;
    uint8_t *frame_region;
    void *stack_top;
    void *frame_base;
    volatile uint64_t marker = 0x123456789abcdef0ULL;
    const uint64_t untouched = 0xa5a5a5a5a5a5a5a5ULL;

    /* Keep stack and frame pages in one bias-relative allocation.  Their
     * fixed relative distance is part of the fixture: ENTER's frame-chain
     * reads then have stable canonical offsets without relying on a fixed
     * guest address. */
    map_region = mmap(NULL, 3 * 4096, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (map_region == MAP_FAILED) {
        return -1;
    }
    stack_region = map_region;
    frame_region = map_region + 4096;
    if (mprotect(frame_region, 4096, PROT_NONE) != 0) {
        munmap(map_region, 3 * 4096);
        return -1;
    }

    /* frame_base - 8 is the first byte of the readable page; frame_base -
     * 16 is the last eight bytes of the protected page.  The trampoline's
     * CALL consumes stack_top - 8, so ENTER's first store lands at -16. */
    stack_top = stack_region + 4096;
    frame_base = frame_region + 4096 + 8;
    *(volatile uint64_t *)((uint8_t *)stack_top - 16) = untouched;
    sa.sa_handler = fault_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;
    if (sigaction(SIGSEGV, &sa, &old_sa) != 0) {
        mprotect(frame_region, 4096, PROT_READ | PROT_WRITE);
        munmap(map_region, 3 * 4096);
        return -1;
    }

    fault_seen = 0;
    if (sigsetjmp(fault_jmp, 1) == 0) {
        enter_on_custom_stack(stack_top, frame_base);
    }

    g_sink ^= marker;
    int first_store_committed =
        *(volatile uint64_t *)((uint8_t *)stack_top - 16) != untouched;
    if (sigaction(SIGSEGV, &old_sa, NULL) != 0) {
        return -1;
    }
    mprotect(frame_region, 4096, PROT_READ | PROT_WRITE);
    munmap(map_region, 3 * 4096);
    return fault_seen && first_store_committed ? 0 : -1;
}

int main(void)
{
    return run_fault() == 0 ? (int)(g_sink & 1) : 1;
}
