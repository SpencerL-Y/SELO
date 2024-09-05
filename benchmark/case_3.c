#include <stdlib.h>


int main(){
    int **p = malloc(sizeof(int*));
    *p = malloc(sizeof(int));
    free(*p);
    free(p);
}