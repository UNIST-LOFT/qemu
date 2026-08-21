/* t25: global uninitialized read: no provenance finding (address is a
 * valid global, not a heap object).  Deterministic rc (no data-dependent
 * branch on the uninitialized byte). */
static char g[8];

int main(void) {
    volatile char c = g[0]; /* uninitialized global read: not address-based */
    (void)c;
    return 0;
}
