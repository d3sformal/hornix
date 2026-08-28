#include <assert.h>

extern int __VERIFIER_nondet_int(void);

int main(void) {
    int length = __VERIFIER_nondet_int();
    if (length < 2 || length > 4) { return 0; }

    int values[length];
    if (__VERIFIER_nondet_int()) {
        values[1] = 7;
    } else {
        values[1] = 9;
    }
    assert(values[1] == 7 || values[1] == 9);
    return 0;
}
