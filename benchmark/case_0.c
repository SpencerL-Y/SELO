#include <stdlib.h>

int main(){
    int whatever;
    int * data = malloc(sizeof(int));
    int data2[10];
    *(data + 1) = whatever;
    int n = *(data + 1);
    if(n > 0) {
        free(data);
    }
}
