/* t19: PLT child trace: after the entrypoint, the guest forks; the child
 * must be traced with its own allocation.  Parent and child both run.
 * No bug: expect a normal result (child exit status is observed). */
#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

int main(void) {
    pid_t pid = fork();
    if (pid == 0) {
        char *p = malloc(8);
        if (p) free(p);
        _exit(0);
    }
    int st;
    waitpid(pid, &st, 0);
    return 0;
}
