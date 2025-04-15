#include <assert.h>

unsigned char test() {
    return 0;
}

int main() {
  unsigned char n = test();
  if (n == 0) {
    return 0;
  }
  assert(0);
}
