#include <assert.h>

int max(int a, int b)
{
  int c;
  if (a > b)
    c = a;
  else
    c = b;

  assert(c >= a && c >= b);
  return c;
}

int main()
{
  int m = max(1, 2);
  return 1;
}