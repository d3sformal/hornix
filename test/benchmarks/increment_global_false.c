#include <assert.h>

extern int __VERIFIER_nondet_int(void);

int global = 0;

void increment() {
    global += 1;
}

int main() {
    global = __VERIFIER_nondet_int();

    int old_value = global;

    if (old_value > 100)
        return 0;

    increment();

    assert(global == old_value);

    return 0;
}

