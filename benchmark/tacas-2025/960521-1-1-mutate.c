#include <stdlib.h>
int *a, *b;
int n;
int main ()
{
  n = 3;
  a = malloc (n * sizeof(*a));
  b = malloc (n * sizeof(*b));
  *b++ = 0;
  if (b[-1])
  { free(a); free(b); }
  else
  { free(a); free(b); } // invalid free
  return 0;
}