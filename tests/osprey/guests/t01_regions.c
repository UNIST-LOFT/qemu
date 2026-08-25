/* t01_regions: Stage-1 canonical-region fixture.
 *
 * Exercises the Stage-1 identity/lifecycle contract:
 *  - .data and .bss globals (one merged canonical G region);
 *  - recursion (recurse(3) -> 4 live frames of the same function);
 *  - two allocations at one site (same H_site, distinct instances);
 *  - same-base reuse (free + realloc at the same address);
 *  - realloc success (old object retired, new object created);
 *  - realloc(p, 0) (old object retired, NULL return).
 *
 * The harness runs the guest twice and compares the canonical fact
 * dumps byte-identically (PIE determinism / ASLR invariance), then
 * asserts the expected canonical rows.
 */
#include <stdlib.h>

static int g_data[4] = { 1, 2, 3, 4 };   /* .data */
static int g_bss[4];                     /* .bss */

static volatile int g_sink;

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

    /* Two allocations at one site (the malloc inside alloc32). */
    char *a = alloc32();
    char *b = alloc32();
    if (!a || !b) return 0;
    a[0] = 1;
    b[0] = 2;
    g_sink = a[0] + b[0];

    /* Same-base reuse: free a, then realloc returns the same address. */
    free(a);
    char *c = malloc(32);
    if (!c) return 0;
    c[0] = 3;
    g_sink = c[0];

    /* realloc success: old object retired, new object created. */
    char *d = malloc(16);
    if (!d) return 0;
    d[0] = 4;
    char *e = realloc(d, 64);
    if (!e) return 0;
    e[0] = 5;
    g_sink = e[0];

    /* realloc(p, 0): glibc frees p and returns NULL. */
    char *f = malloc(8);
    if (!f) return 0;
    f[0] = 6;
    char *g = realloc(f, 0);
    (void)g;

    free(b);
    free(c);
    free(e);
    return 0;
}
