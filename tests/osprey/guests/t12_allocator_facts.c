/* t12_allocator_facts: Stage-2.5 allocator-fact matrix.
 *
 * Every allocator call goes through a noinline wrapper so the modeled PLT
 * path observes stable return sites.  Failure operands are volatile to keep
 * overflow and allocation-failure cases concrete without compiler folding.
 */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>

static volatile unsigned g_sink;

__attribute__((noinline)) static void *call_malloc(size_t size)
{
    return malloc(size);
}

__attribute__((noinline)) static void *call_calloc(size_t count,
                                                    size_t element_size)
{
    return calloc(count, element_size);
}

__attribute__((noinline)) static void *call_realloc_resize(void *ptr,
                                                            size_t size)
{
    return realloc(ptr, size);
}

__attribute__((noinline)) static void *call_realloc_fail(void *ptr,
                                                          size_t size)
{
    return realloc(ptr, size);
}

__attribute__((noinline)) static void *call_realloc_zero(void *ptr,
                                                          size_t size)
{
    return realloc(ptr, size);
}

__attribute__((noinline)) static void call_free(void *ptr)
{
    free(ptr);
}

static void touch_realloc_success(unsigned char *ptr, unsigned value);
static void touch_failed_realloc_survivor(unsigned char *ptr, unsigned value);

__attribute__((noinline)) static void touch_byte(unsigned char *ptr,
                                                  unsigned value)
{
    if (ptr != NULL) {
        ptr[0] = (unsigned char)value;
        g_sink += ptr[0];
    }
}

int main(void)
{
    /* Repeated malloc(24) at one modeled call site. */
    void *repeat1 = call_malloc(24);
    void *repeat2 = call_malloc(24);
    void *repeat3 = call_malloc(24);

    /* One modeled malloc site with three successful requested sizes. */
    volatile size_t size16 = 16;
    volatile size_t size32 = 32;
    volatile size_t size48 = 48;
    void *variable16 = call_malloc(size16);
    void *variable32 = call_malloc(size32);
    void *variable48 = call_malloc(size48);

    /* Positive calloc geometry, including two same-total geometries at
     * the same modeled call site. */
    void *calloc316 = call_calloc(3, 16);
    void *calloc124 = call_calloc(1, 24);
    void *calloc_same1 = call_calloc(3, 16);
    void *calloc_same2 = call_calloc(2, 24);

    /* Zero geometry remains a successful F05 observation when libc returns
     * non-NULL, but never becomes F06 evidence. */
    volatile size_t zero = 0;
    void *calloc_zero_count = call_calloc(zero, 16);
    void *calloc_zero_element = call_calloc(4, zero);

    /* Successful nonzero realloc publishes only the replacement object. */
    void *resized = call_malloc(40);
    resized = call_realloc_resize(resized, 80);
    touch_realloc_success(resized, 1);

    /* Failed nonzero realloc leaves the old object live and usable. */
    void *survivor = call_malloc(8);
    touch_byte(survivor, 2);
    volatile size_t impossible = (size_t)-1;
    void *failed = call_realloc_fail(survivor, impossible);
    if (failed != NULL) {
        call_free(failed);
        return 1;
    }
    touch_failed_realloc_survivor(survivor, 3);

    /* realloc(p, 0) is the deallocation-without-replacement case on the
     * test libc; no replacement fact is expected when it returns NULL. */
    void *zero_realloc_source = call_malloc(8);
    void *zero_realloc = call_realloc_zero(zero_realloc_source, zero);
    if (zero_realloc != NULL) {
        call_free(zero_realloc);
    }

    /* A non-NULL malloc(0) is an exact successful zero-size F05. */
    void *malloc_zero = call_malloc(0);
    if (malloc_zero == NULL) {
        return 2;
    }

    /* calloc overflow is diagnosed without a wrapped allocation object. */
    volatile size_t huge = (size_t)-1;
    volatile size_t two = 2;
    void *overflow = call_calloc(huge, two);
    if (overflow != NULL) {
        call_free(overflow);
        return 3;
    }

    call_free(repeat1);
    call_free(repeat2);
    call_free(repeat3);
    call_free(variable16);
    call_free(variable32);
    call_free(variable48);
    call_free(calloc316);
    call_free(calloc124);
    call_free(calloc_same1);
    call_free(calloc_same2);
    call_free(calloc_zero_count);
    call_free(calloc_zero_element);
    call_free(resized);
    call_free(survivor);
    call_free(malloc_zero);

    /* Avoid exit-time libc activity changing the checked-in dump. */
    _exit(0);
}

/* Keep these probes after main: replacing same-size call instructions above
 * does not shift the established allocator/model sites.  The global labels
 * identify the exact memory instruction whose canonical heap owner proves
 * the realloc lifecycle at access time. */
__attribute__((noinline)) static void
touch_realloc_success(unsigned char *ptr, unsigned value)
{
    (void)value;
    if (ptr != NULL) {
        __asm__ volatile(
            ".globl t12_realloc_success_access\n"
            "t12_realloc_success_access:\n\t"
            "movb $1, (%0)"
            :
            : "r"(ptr)
            : "memory");
    }
}

__attribute__((noinline)) static void
touch_failed_realloc_survivor(unsigned char *ptr, unsigned value)
{
    (void)value;
    if (ptr != NULL) {
        __asm__ volatile(
            ".globl t12_failed_realloc_survivor_access\n"
            "t12_failed_realloc_survivor_access:\n\t"
            "movb $3, (%0)"
            :
            : "r"(ptr)
            : "memory");
    }
}
