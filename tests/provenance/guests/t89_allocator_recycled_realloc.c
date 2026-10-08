/* Clean 10268 control: libc sorting recycles a 1224-byte scratch chunk, then
 * realloc moves a live payload into allocator-owned storage. No stale pointer
 * is dereferenced. Run with production libc-inclusive model metadata.
 * The exact nested-copy reproduction requires glibc's allocating qsort path
 * (observed with Guix glibc 2.41); the movement/data checks are mandatory on
 * every libc, rather than silently accepting a nonmoving control.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int compare(const void *a, const void *b)
{
    uint64_t x = *(const uint64_t *)a;
    uint64_t y = *(const uint64_t *)b;
    return (x > y) - (x < y);
}

int main(void)
{
    /* Resolve the guest memcpy PLT/GOT before realloc's internal call. IFUNC
     * resolver addresses must not be substituted for the selected body. */
    char source[2] = {'x', 'y'}, destination[2];
    memcpy(destination, source, sizeof(source));
    if (destination[1] != 'y') return 89;

    uint64_t *p = malloc(153 * sizeof(*p));
    if (!p) return 90;
    for (size_t i = 0; i < 153; ++i) p[i] = 153 - i;
    qsort(p, 152, sizeof(*p), compare);
    void *block1 = malloc(48), *block2 = malloc(32);
    if (!block1 || !block2) return 91;
    uint64_t *q = realloc(p, 153 * sizeof(*p));
    if (!q) return 92;
    qsort(q, 153, sizeof(*q), compare);
    void *block3 = malloc(48), *block4 = malloc(32);
    if (!block3 || !block4) return 93;
    uintptr_t before = (uintptr_t)q;
    uint64_t *r = realloc(q, 154 * sizeof(*q));
    if (!r) return 94;
    int moved = (uintptr_t)r != before;
    for (size_t i = 0; i < 153; ++i)
        if (r[i] != i + 1) return 95;
    r[153] = 154;
    fprintf(stderr, "allocator-control moved=%d preserved=153 size=1232\n", moved);
    free(r);
    free(block1);
    free(block2);
    free(block3);
    free(block4);
    return moved ? 0 : 96;
}
