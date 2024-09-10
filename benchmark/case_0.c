#include <stdlib.h>

int main(){
    // int * data = malloc(sizeof(int));
    // int * data2 = malloc(2*sizeof(int));  
    // free(data);
    // int i = *(data + 1);
    int *q = malloc(sizeof(int));
    int ** p = malloc(sizeof(int*));
   
    *p = q;
    **p = 100;
    return 0;
    // int* j = NULL;
    // int* i = j;
    // // *(data + 1) = whatever;
    // int n = *(data+1);
    // if(i > 0) {
    //     free(data);
    // }
}
