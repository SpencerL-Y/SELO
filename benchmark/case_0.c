#include <stdlib.h>

int main(){
    // int whatever;
    int * data = malloc(2*sizeof(int));
    // // *(data + 1) = whatever;
    int n = *(data+1);
    // if(n > 0) {
    //     free(data);
    // }
}
