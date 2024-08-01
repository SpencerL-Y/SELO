#include <stdlib.h>

int main(){
    // int whatever;
    int * data = malloc(sizeof(int));
    int * data2 = malloc(2*sizeof(int));  
    free(data);
    int i = *(data);
    // int* j = NULL;
    // int* i = j;
    // // *(data + 1) = whatever;
    // int n = *(data+1);
    // if(i > 0) {
    //     free(data);
    // }
}
