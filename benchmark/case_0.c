#include <stdlib.h>

int main(){
    int * data = malloc(sizeof(int));
    int * data2 = malloc(2*sizeof(int));  
    free(data);
    int i = *(data + 1);
}
