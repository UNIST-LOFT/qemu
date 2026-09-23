/* t81: the PLT_INFO_FILE model table is keyed by the executable's basename,
 * and BinRadar executes derived artifacts of that executable
 * (<binary>.brpatched / <binary>.brcached) which share its exact PLT
 * layout.  Before this was handled, `load_image` compared raw basenames, so
 * a table generated for `<binary>.orig` registered no model at all for an
 * artifact run: the allocator hooks went silent and a real heap OOB/UAF
 * disappeared (a normal exit instead of a finding).
 *
 * This guest reproduces that situation without any patch artifact: copies
 * named .orig and .brpatched have identical PLT layouts; PLT_INFO_FILE is
 * generated from the .orig copy, then the .brpatched copy executes.  The
 * finding must still be published.
 *
 * A copy of the binary is made by the test driver; this source only has to
 * perform the violation.
 */
#include <stdlib.h>

int main(void) {
    char *p = malloc(8);
    if (p == NULL) {
        return 1;
    }
    /* Write one byte past the allocation: a heap-buffer-overflow the
     * allocator-hook provenance path detects only when malloc/free were
     * resolved through PLT_INFO_FILE. */
    p[8] = 1;
    free(p);
    return 0;
}
