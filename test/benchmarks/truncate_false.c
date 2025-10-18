#include <assert.h>
extern unsigned char __VERIFIER_nondet_uchar(void);
int main() {
  unsigned char n = __VERIFIER_nondet_uchar();
  unsigned char m = __VERIFIER_nondet_uchar();
  unsigned char sum = m + n;
  assert(sum >= m);
  return 0;
}
