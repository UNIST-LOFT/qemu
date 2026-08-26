/* t01_regions: Stage-1 canonical-region fixture.
 *
 * Exercises the Stage-1 identity/lifecycle contract:
 *  - .data and .bss globals (one merged canonical G region);
 *  - recursion (recurse(3) -> 4 live frames of the same function);
 *  - two allocations at one site (same H_site, distinct instances);
 *  - successful same-base reuse (free + malloc at the same address,
 *    glibc tcache LIFO: deterministic);
 *  - realloc success with a forced move (16 -> 1 MiB, above the mmap
 *    threshold: glibc cannot grow the 16-byte chunk in place, so the
 *    new object is at a distinct base — deterministic, and never
 *    depends on glibc choosing in-place realloc);
 *  - failed realloc preserving the old identity (huge size -> NULL,
 *    old object stays live and usable);
 *  - realloc(p, 0) (old object retired, NULL return);
 *  - zero-size non-NULL malloc(0) (unique pointer, extent 0).
 *  - ret imm16 stack cleanup followed by a caller-stack access (the
 *    generic RSP hook must not pre-pop before the explicit RET hook).
 *
 * The harness runs the guest three times with distinct PIE load biases
 * (default + two forced BINRADAR_MMAP_START values) and compares the
 * canonical fact dumps byte-identically, then compares against the
 * checked-in exact canonical rows (t01_regions.expected).
 */
#include <stdlib.h>
#include <unistd.h>

static int g_data[4] = { 1, 2, 3, 4 };   /* .data */
static int g_bss[4];                     /* .bss */

static volatile int g_sink;

static void ret16_callee(void);

static int recurse(int n) {
    int local[2] = { n, n + 1 };
    if (n <= 0) {
        return local[0];
    }
    return recurse(n - 1) + local[1];
}

/* Two allocations at ONE call site (the malloc inside this helper). */
static char *alloc32(void) {
    return malloc(32);
}

int main(void) {
    /* .data + .bss globals: distinct addresses, one canonical G. */
    g_data[0] = g_data[1] + g_data[2];
    g_bss[0] = g_data[0];
    g_bss[3] = g_bss[0] + 1;

    /* Recursion: 4 live frames of recurse at the deepest point. */
    g_sink = recurse(3);

    /* Two live allocations at one site (the malloc inside alloc32). */
    char *a = alloc32();
    char *b = alloc32();
    if (!a || !b) return 0;
    a[0] = 1;
    b[0] = 2;
    g_sink = a[0] + b[0];

    /* Successful same-base reuse: free a, then malloc(32) returns the
     * same address (glibc tcache LIFO for the same size class). */
    free(a);
    char *c = malloc(32);
    if (!c) return 0;
    c[0] = 3;
    g_sink = c[0];

    /* realloc success with a forced move: 16 -> 1 MiB.  The new size is
     * above the glibc mmap threshold, so the chunk cannot grow in
     * place; the new object is at a distinct base.  The lifecycle rows
     * (old retired, new object with the requested size) are
     * deterministic and never depend on glibc choosing in-place
     * realloc. */
    char *d = malloc(16);
    if (!d) return 0;
    d[0] = 4;
    char *e = realloc(d, 1024 * 1024);
    if (!e) return 0;
    e[0] = 5;
    g_sink = e[0];

    /* Failed realloc preserving the old identity: a huge size makes
     * glibc fail with ENOMEM and return NULL; the old object stays
     * live and usable. */
    char *f = malloc(8);
    if (!f) return 0;
    f[0] = 6;
    char *g = realloc(f, (size_t)-1);
    if (g) return 0;   /* must fail */
    f[0] = 7;          /* old pointer still usable */
    g_sink = f[0];

    /* realloc(p, 0): glibc frees p and returns NULL. */
    char *h = malloc(8);
    if (!h) return 0;
    h[0] = 8;
    char *i = realloc(h, 0);
    (void)i;

    /* Zero-size non-NULL: glibc malloc(0) returns a unique pointer. */
    char *z = malloc(0);
    if (!z) return 0;
    g_sink = (z != NULL);

    free(b);
    free(c);
    free(e);
    free(f);
    free(z);

    __asm__ volatile(
        "subq $16, %%rsp\n\t"
        "call ret16_callee\n\t"
        "movq (%%rsp), %%rax\n\t"
        :
        :
        : "rax", "cc", "memory");

    /* _exit: no atexit handlers, no global dtors, no _fini.  The exit
     * path is bias-dependent (the child can fault at different points
     * depending on the stack position), so the fixture must not
     * exercise it: the canonical dump must be byte-identical across
     * forced PIE biases. */
    _exit(0);
}

/* Stage-1 return-lifecycle regression.  The caller reserves the 16 bytes
 * discarded by `ret $16`; after return, a stack load proves that RET-imm
 * popped only this activation and did not let generic RSP resynchronization
 * pre-pop it before the explicit return hook. */
__attribute__((used, naked, noinline))
static void ret16_callee(void) {
    __asm__ volatile("ret $16");
}
