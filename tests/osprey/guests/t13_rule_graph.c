/* t13_rule_graph: canonical Stage-3 relation and graph fixture.
 *
 * The guest deliberately keeps all probes small and deterministic:
 *   - two modeled copies establish an R10 data-flow hint;
 *   - two noinline load sites each observe source/destination fields for R11;
 *   - one global pointer cell targets both structures, with matching F02
 *     BaseAddr observations for R12 and CD11;
 *   - calloc, constant malloc, and varied malloc sites exercise CB01/CC01/
 *     CC02 and heap-field rules.
 *
 * Probe helpers are after main so changing the call sequence above does not
 * move the modeled allocator and memory sites.  The harness runs this PIE
 * binary under three loader biases and compares both canonical dumps.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static uint64_t g_source[4] __attribute__((aligned(8)));
static uint64_t g_destination[4] __attribute__((aligned(8)));
static void *g_pointer_cell __attribute__((aligned(8)));
static volatile uint64_t g_sink;

static void *call_constant_malloc(size_t size);
static void *call_varied_malloc(size_t size);
static void *call_positive_calloc(size_t count, size_t size);
static uint64_t read_source_field(uint64_t *value);
static uint64_t read_destination_field(uint64_t *value);

int main(void)
{
    for (unsigned i = 0; i < 4; i++) {
        g_source[i] = 0x1111111111111111ULL * (i + 1);
        g_destination[i] = 0;
    }

    /* R10: equal-width copies with the same positive source/destination
     * displacement. */
    memcpy(g_destination, g_source, sizeof(uint64_t));
    memcpy(g_destination + 2, g_source + 2, sizeof(uint64_t));

    /* R11: each noinline instruction observes two same-width chunks. */
    g_sink ^= read_source_field(g_source);
    g_sink ^= read_source_field(g_destination);
    g_sink ^= read_destination_field(g_source + 2);
    g_sink ^= read_destination_field(g_destination + 2);

    /* F04/R12: one pointer cell takes two structure bases. */
    __asm__ volatile(
        "leaq g_source(%%rip), %%r12\n\t"
        ".globl t13_pointer_source\n"
        "t13_pointer_source:\n\t"
        "movq %%r12, g_pointer_cell(%%rip)\n"
        : : : "r12", "memory");
    __asm__ volatile(
        "leaq g_destination(%%rip), %%r12\n\t"
        ".globl t13_pointer_destination\n"
        "t13_pointer_destination:\n\t"
        "movq %%r12, g_pointer_cell(%%rip)\n"
        : : : "r12", "memory");

    /* F02/R12 BaseAddr evidence at field offset eight, followed by accesses
     * at each corresponding structure base for CD06/CD11. */
    __asm__ volatile(
        "leaq g_source(%%rip), %%r12\n\t"
        ".globl t13_source_field_access\n"
        "t13_source_field_access:\n\t"
        "movq 8(%%r12), %%r13\n\t"
        : : : "r12", "r13", "memory");
    __asm__ volatile(
        "leaq g_destination(%%rip), %%r12\n\t"
        ".globl t13_destination_field_access\n"
        "t13_destination_field_access:\n\t"
        "movq 8(%%r12), %%r13\n\t"
        : : : "r12", "r13", "memory");
    __asm__ volatile(
        "leaq g_source(%%rip), %%r12\n\t"
        ".globl t13_source_base_access\n"
        "t13_source_base_access:\n\t"
        "movq (%%r12), %%r13\n\t"
        : : : "r12", "r13", "memory");
    __asm__ volatile(
        "leaq g_destination(%%rip), %%r12\n\t"
        ".globl t13_destination_base_access\n"
        "t13_destination_base_access:\n\t"
        "movq (%%r12), %%r13\n\t"
        : : : "r12", "r13", "memory");

    /* R08/CC01: repeated successful allocations at one call site with one
     * size.  R09/CC02: distinct successful sizes at a separate site. */
    void *constant_a = call_constant_malloc(24);
    void *constant_b = call_constant_malloc(24);
    volatile size_t varied_a_size = 16;
    volatile size_t varied_b_size = 32;
    volatile size_t varied_c_size = 64;
    void *varied_a = call_varied_malloc(varied_a_size);
    void *varied_b = call_varied_malloc(varied_b_size);
    void *varied_c = call_varied_malloc(varied_c_size);
    if (constant_a == NULL || constant_b == NULL || varied_a == NULL ||
        varied_b == NULL || varied_c == NULL) {
        _exit(1);
    }

    /* Positive F06 geometry and a heap field access. */
    void *array = call_positive_calloc(2, 16);
    if (array == NULL) _exit(1);
    ((volatile uint64_t *)array)[0] = 0xabcdef;
    ((volatile uint64_t *)varied_c)[1] = 0x123456;
    g_sink ^= ((volatile uint64_t *)array)[0];

    (void)g_sink;
    _exit(0);
}

/* Keep allocator and load helpers after main. */
__attribute__((noinline)) static void *call_constant_malloc(size_t size)
{
    return malloc(size);
}

__attribute__((noinline)) static void *call_varied_malloc(size_t size)
{
    return malloc(size);
}

__attribute__((noinline)) static void *call_positive_calloc(size_t count,
                                                              size_t size)
{
    return calloc(count, size);
}

__attribute__((noinline)) static uint64_t read_source_field(uint64_t *value)
{
    return *value;
}

__attribute__((noinline)) static uint64_t read_destination_field(
    uint64_t *value)
{
    return *value;
}
