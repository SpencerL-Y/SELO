#include <stdlib.h>
typedef struct {
    void *lo;
    int hi;
} TData;

int main(){
    TData data;
    TData* pdata = &data;

    TData c;
    pdata->lo = malloc(16);
    pdata->hi = malloc(24);
    void *lo = pdata->lo;
    int hi = pdata->hi;
    if(lo == hi){
        free(lo);
        free(hi);
    }
}