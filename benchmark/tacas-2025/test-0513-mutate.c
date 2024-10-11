#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
struct DItem {
    struct DItem* next;
    int value;
};
struct TLItem {
    struct TLItem* next;
    struct DItem* data;
};
int main() {
    struct TLItem* data = ((void *)0);
    struct DItem* item, * item2;
    struct TLItem *lItem;
    // while (__VERIFIER_nondet_int()) {
        item = malloc(sizeof *item);
        item->next = ((void *)0);
        item->value = __VERIFIER_nondet_int();
        lItem = malloc(sizeof *lItem);
            lItem->next = lItem;
            data = lItem;
        lItem->data = item;
        item = ((void *)0);
        lItem = ((void *)0);
    // }
    if (!data)
        return 0;
    if(data->next != data) {
        item = data->data;
        item2 = data->next->data;
        lItem = data->next;
        data->next = lItem->next;
        free(lItem);
        struct DItem** dst = &data->data;
        if (item && item2) {
            if (item->value < item2->value) {
                *dst = item;
                item = item->next;
            } else {
                // go here
                *dst = item2;
                item2 = item2->next;
            }
            dst = &(*dst)->next;
        }
        if (item) {
            *dst = item;
            item = ((void *)0);
        } else if (item2) {
            *dst = item2;
            item2 = ((void *)0);
        }
        dst = ((void *)0);
        data = data->next;
    }
    item = data->data;
    free(data);
    if (item) {
        item2 = item;
        item = item->next;
        free(item2);
    }
    return 0;
}

// safe