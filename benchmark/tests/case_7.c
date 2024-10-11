#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int* f()
{
  int array_size = 3;

  int* numbers = (int*) alloca(array_size * sizeof(int));
	
  for(int k = 0; k < array_size; k++)
  {
    numbers[k] = __VERIFIER_nondet_int();
  }
  return numbers;
}

int main()
{
  int* p = f();
  free(p);
  return 0;
}
