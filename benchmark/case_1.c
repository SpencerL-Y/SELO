#include <stdlib.h>

typedef struct {
    void *lo;
    void *hi;
} TData;

int main() {
    TData * p1 = malloc(sizeof(TData));
    p1->lo = malloc(12);
    p1->hi = malloc(12);
    void * p2;
    int x;
    if (x) p2 = p1->hi;
    else p2 = p1->lo;
    free(p2);
    return 0;
}