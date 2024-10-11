extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

#include <stdlib.h>

typedef struct {
    void *lo;
    void *hi;
} TData;

TData* create_node()
{
    TData data;
    return &data;
}

int main() {
    TData *p1 = create_node();
    TData *p2 = create_node();
    free(p1);
    free(p2);
    return 0;
}
