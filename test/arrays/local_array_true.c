#include <assert.h>

extern int __VERIFIER_nondet_int(void);

int main(void) {
    int length = __VERIFIER_nondet_int();
    if (length < 1 || length > 4) { return 0; }

    int values[length];
    values[0] = 42;
    assert(values[0] == 42);
    return 0;
}
