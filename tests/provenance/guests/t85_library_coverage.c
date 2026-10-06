#include <stdint.h>
#include <stdlib.h>
#include <string.h>

extern uint64_t coverage_span(const char *p);

int main(int argc, char **argv)
{
    size_t size = argc > 1 ? 16 : 8;
    char *data = malloc(size);
    if (!data) return 2;
    memset(data, 'A', size);
    uint64_t value;
    __asm__ volatile("call coverage_span@PLT\n"
                     ".global library_call_return\nlibrary_call_return:"
                     : "=a"(value), "+D"(data)
                     :
                     : "rcx", "rdx", "rsi", "r8", "r9", "r10", "r11", "memory");
    if (argc > 1 && value != UINT64_C(0x4141414141414141)) return 3;
    free(data);
    return 0;
}
