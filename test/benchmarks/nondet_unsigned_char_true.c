#include <assert.h>
extern unsigned char __VERIFIER_nondet_uchar(void);
int main() {
  unsigned char v = __VERIFIER_nondet_uchar();
  if (v > 65025) {
    assert(0);
    return 1;
  }
  return 0;
}

