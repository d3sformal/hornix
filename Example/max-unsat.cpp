#include <assert.h>

void max(int a, int b)
{
  int c;
  if (a > b)
    c = a;
  else
    c = b;

  assert(c <= a && c <= b);
}

int main()
{
  max(1, 2);
  return 1;
}