#include <stdlib.h>

int main(){
    // int whatever;
    int * data = malloc(2 * sizeof(int));
    int * data2 = malloc(2 * sizeof(int));
    free(data2);
    int i = *(data2 + 1);
}
