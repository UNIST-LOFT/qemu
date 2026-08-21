/* t03: stack pointers are not tracked — a dangling stack pointer write
 * must NOT produce a finding (no false positive). */
int main(void) {
    char *p = __builtin_alloca(8);
    p[0] = 1; /* in-bounds stack access; tracer only tracks heap */
    return 0;
}
