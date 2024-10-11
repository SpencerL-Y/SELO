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
    free(create_node());
    return 0;
}
