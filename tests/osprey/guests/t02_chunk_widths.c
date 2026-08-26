/* t02_chunk_widths: Stage-1 canonical-width fixture.
 *
 * Exercises a representative subset of F01 access widths currently
 * routed through the shared semantic layer:
 *  - integer stores of every width (b/w/l/q) at one site;
 *  - atomic RMW (lock xadd / lock cmpxchg) full-width stores;
 *  - 64-bit (non-lock) cmpxchg/xadd paired stores (two 4-byte
 *    halves merged into one 8-byte fact);
 *  - SSE 16-byte stores (movaps) and 8-byte halves (movsd);
 *  - x87 stores: fstl (8), fstpt (10), fbstp (10);
 *  - fnstenv (14) and fsave (94) 16-bit-mode sizes are exercised on
 *    the i386 build; on x86_64 the same opcodes store 28/108 bytes;
 *  - a labeled byte store to a read-only main-image page faults and must
 *    not contribute an F01 row.
 *
 * The harness asserts that every access fact carries the exact chunk
 * width for the emitting opcode: a fact with a size that is not a
 * power of two must be one of the known x87 helper widths, and each
 * opcode family contributes at least one fact at its canonical size.
 */
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

static volatile uint64_t g_sink;
static sigjmp_buf fault_jmp;
static volatile sig_atomic_t fault_seen;

/* One call site per width: a 16-byte aligned buffer, integer stores
 * of each width land at distinct offsets (facts key on (pc, size)). */
static __attribute__((aligned(32))) uint8_t buf[384];
static __attribute__((aligned(4096))) uint8_t fault_page[4096];

static void fault_handler(int sig)
{
    (void)sig;
    fault_seen = 1;
    siglongjmp(fault_jmp, 1);
}

static __attribute__((noinline)) int faulting_store(void)
{
    struct sigaction sa;
    struct sigaction old_sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = fault_handler;
    sigemptyset(&sa.sa_mask);
    if (sigaction(SIGSEGV, &sa, &old_sa) != 0 ||
        mprotect(fault_page, sizeof(fault_page), PROT_READ) != 0) {
        return -1;
    }

    fault_seen = 0;
    if (sigsetjmp(fault_jmp, 1) == 0) {
        __asm__ volatile(
            ".globl t02_fault_store\n"
            "t02_fault_store:\n"
            "movb $0x5a, (%0)\n"
            :: "r"(fault_page) : "memory");
    }

    int restore_ok = mprotect(fault_page, sizeof(fault_page),
                              PROT_READ | PROT_WRITE) == 0;
    int handler_ok = sigaction(SIGSEGV, &old_sa, NULL) == 0;
    return fault_seen && restore_ok && handler_ok ? 0 : -1;
}

static void int_stores(void) {
    uint8_t *p = buf;
    *(volatile uint8_t *)p = 0x11;
    *(volatile uint16_t *)(p + 16) = 0x2222;
    *(volatile uint32_t *)(p + 32) = 0x33333333;
    *(volatile uint64_t *)(p + 48) = 0x4444444444444444ULL;
    g_sink = *(volatile uint64_t *)(p + 48);
}

static void atomic_rmw(void) {
    volatile uint32_t *p = (volatile uint32_t *)(buf + 64);
    *p = 0;
    __atomic_add_fetch(p, 1, __ATOMIC_SEQ_CST);
    __atomic_compare_exchange_n(p, &(uint32_t){0}, 5, 0,
                                __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
    g_sink = *p;
}

static void atomic_rmw64(void) {
    volatile uint64_t *p = (volatile uint64_t *)(buf + 80);
    *p = 0;
    __atomic_add_fetch(p, 1, __ATOMIC_SEQ_CST);
    __atomic_compare_exchange_n(p, &(uint64_t){0}, 9, 0,
                                __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
    g_sink = *p;
}

static void paired_64(void) {
    /* cmpxchg8b: the 8-byte RMW is one F01 fact.  Force the exact
     * opcode with inline asm (compilers emit lock cmpxchg instead). */
    volatile uint64_t *p = (volatile uint64_t *)(buf + 96);
    uint32_t eax = 0, edx = 0, ebx = 0x1111, ecx = 0;
    *p = 0;
    __asm__ volatile(
        "cmpxchg8b %0"
        : "+m"(*p), "+a"(eax), "+d"(edx)
        : "b"(ebx), "c"(ecx)
        : "cc", "memory");
    g_sink = *p;
}

static void sse_stores(void) {
    /* 16-byte movaps store: one 16-byte fact (fault-safe: the F01
     * event is emitted after both 8-byte halves). */
    __asm__ volatile(
        "movaps %%xmm0, (%0)" :: "r"(buf + 128) : "memory");
    g_sink = *(volatile uint64_t *)(buf + 128);
    /* 8-byte movsd store: one 8-byte fact. */
    __asm__ volatile(
        "movsd %%xmm0, (%0)" :: "r"(buf + 144) : "memory");
    g_sink = *(volatile uint64_t *)(buf + 144);
}

static void x87_stores(void) {
    __asm__ volatile("fstl %0" : "=m"(*(double *)(buf + 160)));
    __asm__ volatile("fstpt %0" : "=m"(*(long double *)(buf + 176)));
    __asm__ volatile("fbstp %0" : "=m"(*(long double *)(buf + 192)));
    __asm__ volatile("fnstenv %0" : "=m"(*(uint8_t(*)[28])(buf + 208)));
    __asm__ volatile("fnsave %0" : "=m"(*(uint8_t(*)[108])(buf + 236)));
    g_sink = *(volatile uint64_t *)(buf + 160);
}

int main(void) {
    if (faulting_store() != 0) {
        return 2;
    }
    int_stores();
    atomic_rmw();
    atomic_rmw64();
    paired_64();
    sse_stores();
    x87_stores();
    return (int)(g_sink & 1);
}
