/* t17: free(NULL) must be a no-op. */
#include <stdlib.h>

int main(void) {
    free(NULL);
    return 0;
}
