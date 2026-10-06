#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern uint64_t coverage_span(const char *p);
extern uint64_t coverage_nested(const char *p);
extern uint64_t coverage_callback(const char *p, uint64_t (*callback)(const char *));
extern void *coverage_access_address(void);
extern void *coverage_signal_address(void);
extern void *coverage_inner_return_address(void);

#ifdef COVERAGE_STANDALONE_ENTRY
/* Enter without CRT's _start->__libc_start_main frame. Merely tail-jumping
 * from main leaves that legitimate outer main-image boundary alive. */
__asm__(".global coverage_start_entry\ncoverage_start_entry:\n"
        "subq $8, %rsp\n jmp main\n");
int main(void)
{
    char *data = malloc(8);
    if (!data) _Exit(2);
    memset(data, 'A', 8);
    fprintf(stderr, "[fixture] [actual_pc %lx] [inner_return %lx]\n",
            (unsigned long)(COVERAGE_STANDALONE_ENTRY == 2
                            ? coverage_signal_address() : coverage_access_address()),
            (unsigned long)coverage_inner_return_address());
#if COVERAGE_STANDALONE_ENTRY == 2
    __asm__ volatile("subq $8, %%rsp\n jmp coverage_signal@PLT" : : : "memory");
#else
    __asm__ volatile("subq $8, %%rsp\n jmp coverage_no_caller@PLT"
                     : : "D"(data) : "memory");
#endif
    __builtin_unreachable();
}
#else
/* A live outer main->DSO call must not hide this innermost main boundary. */
__attribute__((noinline)) static uint64_t callback(const char *data)
{
    uint64_t value;
    __asm__ volatile("call coverage_nested@PLT\n"
                     ".global library_callback_return\nlibrary_callback_return:"
                     : "=a"(value), "+D"(data)
                     :
                     : "rcx", "rdx", "rsi", "r8", "r9", "r10", "r11", "memory");
    return value;
}

int main(int argc, char **argv)
{
    const char *mode = argc > 1 ? argv[1] : "direct";
    int benign = strcmp(mode, "benign") == 0;
    size_t size = benign ? 16 : 8;
    char *data = malloc(size);
    if (!data) return 2;
    memset(data, 'A', size);
    fprintf(stderr, "[fixture] [actual_pc %lx] [inner_return %lx]\n",
            (unsigned long)(strcmp(mode, "signal") == 0
                            ? coverage_signal_address() : coverage_access_address()),
            (unsigned long)coverage_inner_return_address());
    uint64_t value;
    if (strcmp(mode, "signal") == 0) {
        __asm__ volatile("call coverage_signal@PLT\n"
                         ".global library_signal_return\nlibrary_signal_return:"
                         : : : "rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "memory");
        return 4;
    } else if (strcmp(mode, "relocated") == 0) {
        void *target = (void *)coverage_span;
        __asm__ volatile("pushq $library_relocated_return\n"
                         ".global library_relocated_jump\nlibrary_relocated_jump:\n"
                         "jmp *%%rax\n"
                         ".global library_relocated_return\nlibrary_relocated_return:"
                         : "=a"(value), "+D"(data)
                         : "0"(target)
                         : "rcx", "rdx", "rsi", "r8", "r9", "r10", "r11", "memory");
    } else if (strcmp(mode, "nested") == 0) {
        __asm__ volatile("call coverage_nested@PLT\n"
                         ".global library_nested_return\nlibrary_nested_return:"
                         : "=a"(value), "+D"(data)
                         :
                         : "rcx", "rdx", "rsi", "r8", "r9", "r10", "r11", "memory");
    } else if (strcmp(mode, "callback") == 0) {
        uint64_t (*target)(const char *) = callback;
        __asm__ volatile("call coverage_callback@PLT\n"
                         ".global library_outer_return\nlibrary_outer_return:"
                         : "=a"(value), "+D"(data), "+S"(target)
                         :
                         : "rcx", "rdx", "r8", "r9", "r10", "r11", "memory");
    } else {
        __asm__ volatile("call coverage_span@PLT\n"
                         ".global library_call_return\nlibrary_call_return:"
                         : "=a"(value), "+D"(data)
                         :
                         : "rcx", "rdx", "rsi", "r8", "r9", "r10", "r11", "memory");
    }
    if (benign && value != UINT64_C(0x4141414141414141)) return 3;
    free(data);
    return 0;
}
#endif
