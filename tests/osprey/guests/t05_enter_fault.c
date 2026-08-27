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
static void enter_on_custom_stack(void *stack_top, void *frame_base)
{
    __asm__ volatile(
        "mov %rsp, %r11\n"
        "mov %rbp, %r10\n"
        "mov %rdi, %rsp\n"
        "mov %rsi, %rbp\n"
        ".globl t05_enter_fault\n"
        "t05_enter_fault:\n"
        "enter $0, $31\n"
        "leave\n"
        "mov %r11, %rsp\n"
        "mov %r10, %rbp\n"
        "ret\n");
}

static int run_fault(void)
{
    struct sigaction sa;
    struct sigaction old_sa;
    uint8_t *stack_region;
    uint8_t *frame_region;
    void *stack_top;
    void *frame_base;
    volatile uint64_t marker = 0x123456789abcdef0ULL;
    const uint64_t untouched = 0xa5a5a5a5a5a5a5a5ULL;

    /* Keep the synthetic stack/frame mappings fixed.  Otherwise the guest
     * mmap allocator shifts the custom frame relative to the host signal
     * stack when the PIE load bias changes, changing canonical S_f offsets
     * and defeating the dump comparison.  NOREPLACE keeps a collision from
     * silently replacing a QEMU/user mapping. */
    stack_region = mmap((void *)0x500000000000ULL, 4096,
                        PROT_READ | PROT_WRITE,
                        MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE,
                        -1, 0);
    frame_region = mmap((void *)0x500000010000ULL, 8192,
                        PROT_READ | PROT_WRITE,
                        MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE,
                        -1, 0);
    if (stack_region == MAP_FAILED || frame_region == MAP_FAILED) {
        if (stack_region != MAP_FAILED) {
            munmap(stack_region, 4096);
        }
        if (frame_region != MAP_FAILED) {
            munmap(frame_region, 8192);
        }
        return -1;
    }
    if (mprotect(frame_region, 4096, PROT_NONE) != 0) {
        munmap(frame_region, 8192);
        munmap(stack_region, 4096);
        return -1;
    }

    /* frame_base - 8 is the first byte of the readable page; frame_base -
     * 16 is the last eight bytes of the protected page. */
    stack_top = stack_region + 4096;
    frame_base = frame_region + 4096 + 8;
    *(volatile uint64_t *)((uint8_t *)stack_top - 8) = untouched;
    sa.sa_handler = fault_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;
    if (sigaction(SIGSEGV, &sa, &old_sa) != 0) {
        return -1;
    }

    fault_seen = 0;
    if (sigsetjmp(fault_jmp, 1) == 0) {
        enter_on_custom_stack(stack_top, frame_base);
    }

    g_sink ^= marker;
    int first_store_committed =
        *(volatile uint64_t *)((uint8_t *)stack_top - 8) != untouched;
    if (sigaction(SIGSEGV, &old_sa, NULL) != 0) {
        return -1;
    }
    mprotect(frame_region, 4096, PROT_READ | PROT_WRITE);
    munmap(frame_region, 8192);
    munmap(stack_region, 4096);
    return fault_seen && first_store_committed ? 0 : -1;
}

int main(void)
{
    return run_fault() == 0 ? (int)(g_sink & 1) : 1;
}
