/* Raw clone preserves inherited architectural pointer tags in the child. */
#include <linux/sched.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>

static volatile int child_done;

int main(void) {
    char *p = malloc(16);
    void *stack = mmap(NULL, 1 << 20, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_STACK, -1, 0);
    if (!p || stack == MAP_FAILED) return 40;
    free(p);

    register char *tagged __asm__("rbx") = p;
    register volatile int *donep __asm__("r12") = &child_done;
    register long r10 __asm__("r10") = 0;
    register long r8 __asm__("r8") = 0;
    unsigned long flags = CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND |
                          CLONE_THREAD | CLONE_SYSVSEM;
    long result;
    void *stack_top = (void *)(((uintptr_t)stack + (1 << 20)) & ~15UL);

    __asm__ volatile(
        "syscall\n\t"
        "test %%rax, %%rax\n\t"
        "jnz 1f\n\t"
        "movb $1, (%%rbx)\n\t"
        "movl $1, (%%r12)\n\t"
        "mov $60, %%rax\n\t"
        "xor %%rdi, %%rdi\n\t"
        "syscall\n\t"
        "ud2\n"
        "1:"
        : "=a"(result), "+b"(tagged), "+r"(donep)
        : "0"((long)SYS_clone), "D"(flags), "S"(stack_top), "d"(0L),
          "r"(r10), "r"(r8)
        : "rcx", "r11", "cc", "memory");
    if (result < 0) return 41;
    while (!child_done) __asm__ volatile("pause" : : : "memory");
    return 0;
}
