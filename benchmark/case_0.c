#include <stdlib.h>


// typedef struct {
//     int data;
//     int* next;
// } node_t;
typedef struct {
    void* lo;
    void* hi;
} TData;
int main(){
    // node_t node;
    // node.data = 10;
    // node.next = malloc(sizeof(int));
    // node_t* t = (node_t*)malloc(sizeof(node_t));
    // t->data = 10;
    // int whatever;
    // int * data = malloc(sizeof(int));
    // int * data2 = malloc(2*sizeof(int));  
    // free(data);
    // int i = *(data);
    // int* j = NULL;
    // int* i = j;
    // // *(data + 1) = whatever;
    // int n = *(data+1);
    // if(i > 0) {
    //     free(data);
    // }
    TData *p1 = malloc(sizeof(TData));
    p1->lo = malloc(12);
    p1->hi = malloc(12);
    void *p2;
    int x;
    if(x) {
        p2 = p1->hi;
    } else {
        p2 = p1->lo;
    }
    free(p2);
}
