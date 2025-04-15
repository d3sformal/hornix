#include <assert.h>

int max(int a, int b) {
    return a > b ? a : b;
}

int getInt();

int main() {
    int a = getInt();
    int b = getInt();
    int m = max(a,b);
    assert(m >= 0);
}
