/* t02_chunk_widths: Stage-2.2 operation-class regression fixture.
 *
 * Exercises the listed F01 producer families routed through the shared
 * semantic layer.  This is not a complete producer inventory: unsupported
 * ISA extensions are CPUID-gated, and MPX may remain disabled by guest state
 * even when CPUID advertises it.
 *  - integer stores of every width (b/w/l/q) at one site;
 *  - atomic RMW (lock xadd / lock cmpxchg) full-width stores;
 *  - 64-bit (non-lock) cmpxchg/xadd paired stores (two 4-byte
 *    halves merged into one 8-byte fact);
 *  - SSE 16-byte stores (movaps) and 8-byte halves (movsd);
 *  - x87 stores: fstl (8), fstpt (10), fbstp (10);
 *  - fnstenv (14) and fsave (94) 16-bit-mode sizes are exercised on
 *    the i386 build; on x86_64 the same opcodes store 28/108 bytes;
 *  - lock/non-lock xchg, bit-test RMW, lock not/neg, cmpxchg16b;
 *  - MOVD, PEXTR/EXTRACTPS, INSERTPS/PINSR loads, SIMD loads;
 *  - x87 loads, frstor, MXCSR, FXSAVE/FXRSTOR;
 *  - SGDT/SIDT descriptor stores and MPX BNDMOV where supported;
 *  - a labeled byte store to a read-only main-image page faults and must
 *    not contribute an F01 row;
 *  - a labeled 16-byte store commits its first 8-byte TCG half, faults on
 *    the protected second half, and must not contribute an aggregate F01.
 *
 * The harness asserts exact canonical widths and byte-identical rows under
 * three PIE load biases.  Unsupported optional ISA paths are explicit
 * source-inventory entries and are not silently substituted by a different
 * opcode family.
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
static __attribute__((aligned(32))) uint8_t buf[1024];
static __attribute__((aligned(4096))) uint8_t fault_page[4096];
static __attribute__((aligned(4096))) uint8_t paired_fault_pages[8192];

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

static __attribute__((noinline)) int faulting_paired_store(void)
{
    struct sigaction sa;
    struct sigaction old_sa;
    uint8_t *const first_half = paired_fault_pages + 4096 - 8;
    uint8_t *const second_page = paired_fault_pages + 4096;
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = fault_handler;
    sigemptyset(&sa.sa_mask);
    memset(first_half, 0xa5, 8);
    if (sigaction(SIGSEGV, &sa, &old_sa) != 0 ||
        mprotect(second_page, 4096, PROT_READ) != 0) {
        return -1;
    }

    fault_seen = 0;
    if (sigsetjmp(fault_jmp, 1) == 0) {
        __asm__ volatile(
            "pxor %%xmm0, %%xmm0\n\t"
            ".globl t02_fault_paired_store\n"
            "t02_fault_paired_store:\n\t"
            "movups %%xmm0, (%0)\n"
            :: "r"(first_half) : "xmm0", "memory");
    }

    int first_half_written = 1;
    for (int i = 0; i < 8; i++) {
        first_half_written &= first_half[i] == 0;
    }
    int restore_ok = mprotect(second_page, 4096,
                              PROT_READ | PROT_WRITE) == 0;
    int handler_ok = sigaction(SIGSEGV, &old_sa, NULL) == 0;
    return fault_seen && first_half_written && restore_ok && handler_ok
        ? 0 : -1;
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

static void atomic_specials(void) {
    volatile uint64_t *p = (volatile uint64_t *)(buf + 272);
    uint64_t value = 0x1111222233334444ULL;
    *p = 0;
    __asm__ volatile("xchgq %0, (%1)" : "+a"(value) : "r"(p)
                     : "memory");
    __asm__ volatile("lock btsq $3, (%0)" :: "r"(p) : "cc", "memory");
    __asm__ volatile("lock btrq $3, (%0)" :: "r"(p) : "cc", "memory");
    __asm__ volatile("lock btcq $3, (%0)" :: "r"(p) : "cc", "memory");
    __asm__ volatile("lock notq (%0)" :: "r"(p) : "cc", "memory");
    __asm__ volatile("lock negq (%0)" :: "r"(p) : "cc", "memory");

    /* CMPXCHG16B is a single 16-byte paired RMW interval. */
    volatile __int128 *q = (volatile __int128 *)(buf + 288);
    uint64_t eax = 0, edx = 0, ebx = 1, ecx = 0;
    *q = 0;
    __asm__ volatile("lock cmpxchg16b %0" : "+m"(*q), "+a"(eax),
                     "+d"(edx) : "b"(ebx), "c"(ecx) : "cc", "memory");
    g_sink ^= value ^ eax ^ edx;
}

static void special_simd(void) {
    uint32_t word = 0x10203040;
    uint32_t out32;
    uint64_t out64;
    if (!__builtin_cpu_supports("sse4.1")) {
        return;
    }
    __asm__ volatile("movd %1, %%xmm0\n\t"
                     "movd %%xmm0, %0" : "=m"(out32) : "r"(word)
                     : "xmm0", "memory");
    __asm__ volatile("pextrd $1, %%xmm0, %0\n\t"
                     "pextrq $0, %%xmm0, %1" : "=m"(out32), "=m"(out64)
                     : : "xmm0", "memory");
    __asm__ volatile("extractps $2, %%xmm0, %0" : "=m"(out32)
                     : : "xmm0", "memory");
    __asm__ volatile("insertps $0, %0, %%xmm0" :: "m"(word)
                     : "xmm0", "memory");
    __asm__ volatile("pinsrd $1, %0, %%xmm0" :: "m"(word)
                     : "xmm0", "memory");
    __asm__ volatile("pinsrq $0, %0, %%xmm0" :: "m"(out64)
                     : "xmm0", "memory");
    __asm__ volatile("movdqu %1, %%xmm0\n\t"
                     "movdqu %%xmm0, %0" : "=m"(*(uint8_t (*)[16])(buf + 320))
                     : "m"(*(const uint8_t (*)[16])(buf + 128))
                     : "xmm0", "memory");
    g_sink ^= out32 ^ out64;
}

static void movbe_ops(void) {
    uint32_t eax = 1, ebx, ecx, edx;
    uint32_t value = 0x10203040;
    uint32_t output;
    __asm__ volatile("cpuid" : "+a"(eax), "=b"(ebx), "=c"(ecx),
                     "=d"(edx) :: "memory");
    if (!(ecx & (1u << 22))) {
        return;
    }
    __asm__ volatile("movbel %1, %0" : "=m"(*(uint32_t *)(buf + 400))
                     : "r"(value) : "memory");
    __asm__ volatile("movbel %1, %0" : "=r"(output)
                     : "m"(*(const uint32_t *)(buf + 400)) : "memory");
    g_sink ^= output;
}

static void x87_loads_and_state(void) {
    double d = 1.0;
    long double ld = 2.0L;
    uint8_t env_image[108] __attribute__((aligned(16)));
    uint32_t mxcsr = 0x1f80;
    __asm__ volatile("fldl %0" :: "m"(d) : "memory");
    __asm__ volatile("fldt %0" :: "m"(ld) : "memory");
    __asm__ volatile("fnsave %0" : "=m"(env_image) : : "memory");
    __asm__ volatile("frstor %0" :: "m"(env_image) : "memory");
    __asm__ volatile("stmxcsr %0" : "=m"(mxcsr) : : "memory");
    __asm__ volatile("ldmxcsr %0" :: "m"(mxcsr) : "memory");
    g_sink ^= mxcsr;
}

static void descriptor_stores(void) {
    uint8_t gdt[16] __attribute__((aligned(16)));
    uint8_t idt[16] __attribute__((aligned(16)));
    uint16_t ldt;
    __asm__ volatile("sgdt %0" : "=m"(*(uint8_t (*)[10])gdt) : : "memory");
    __asm__ volatile("sidt %0" : "=m"(*(uint8_t (*)[10])idt) : : "memory");
    __asm__ volatile("sldt %0" : "=m"(ldt) : : "memory");
    g_sink ^= gdt[0] ^ idt[0] ^ ldt;
}

static void fxsave_state(void) {
    __asm__ volatile("fxsave %0"
                     : "=m"(*(uint8_t (*)[512])(buf + 512)) : : "memory");
    __asm__ volatile("fxrstor %0"
                     : : "m"(*(const uint8_t (*)[512])(buf + 512))
                     : "memory");
}

static void mpx_pair(void) {
    uint64_t pair[2] __attribute__((aligned(16))) = { 0, 0 };
    uint32_t eax = 7, ebx, ecx = 0, edx;
    __asm__ volatile("cpuid" : "+a"(eax), "=b"(ebx), "+c"(ecx),
                     "=d"(edx) :: "memory");
    if (!(ebx & (1u << 14))) {
        return;
    }
    __asm__ volatile("bndmov %0, %%bnd0" :: "m"(pair) : "memory");
    __asm__ volatile("bndmov %%bnd0, %0" : "=m"(pair) : : "memory");
    g_sink ^= pair[0] ^ pair[1];
}

int main(void) {
    if (faulting_store() != 0) {
        return 2;
    }
    if (faulting_paired_store() != 0) {
        return 3;
    }
    int_stores();
    atomic_rmw();
    atomic_rmw64();
    paired_64();
    sse_stores();
    x87_stores();
    atomic_specials();
    special_simd();
    movbe_ops();
    x87_loads_and_state();
    descriptor_stores();
    fxsave_state();
    mpx_pair();
    return (int)(g_sink & 1);
}
