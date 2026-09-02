#include <assert.h>

void reach_error(void) {
    assert(0);
}

static void check(int value) {
    if (value == 0) {
        reach_error();
    }
    if (value == 1) {
        reach_error();
    }
}

int main(void) {
    check(1);
}
