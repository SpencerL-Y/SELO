#include <stdlib.h>

int main(){

    int num = 5;
    int *i = (int*) malloc(sizeof(int));
    int *j = (int*)malloc(num*sizeof(int)); 
    int *p = NULL;
    if(i == j) {
        free(j);
        p = i;
    } else {
        p = j;
    }
}
