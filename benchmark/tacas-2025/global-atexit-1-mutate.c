#include <stdlib.h>
extern _Bool __VERIFIER_nondet_bool();
int **g = ((void *)0);
void free_g1() {
 free(g);
 g = ((void *)0);
}
void free_g2() {
 if (g != ((void *)0))
  free(*g);
}
void h() {
}
int main() {
 g = (int **) malloc(sizeof(int *));
 if (__VERIFIER_nondet_bool()) return 0; // memory leak
 *g = (int *) malloc(sizeof(int));
 if (__VERIFIER_nondet_bool()) return 0; // memory leak
 free_g1();
 free_g2();
 return 0;
}