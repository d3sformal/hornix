#include <assert.h>

int max(int a, int b) {
    int res = a > b ? a : b;
    assert(res >= 0);
    return res;
}

int getInt();

int main() {
    int a = getInt();
    int b = getInt();
    return max(a,b);
}
