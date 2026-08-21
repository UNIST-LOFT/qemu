/* t23: stack region: accesses to the stack must not be reported
 * (tracer tracks heap only; the stack is not in the region table). */
int main(void) {
    char local[8];
    local[0] = 1;
    return 0;
}
