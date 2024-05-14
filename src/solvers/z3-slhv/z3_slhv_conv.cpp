#include <cassert>
#include <iostream>
#include <z3_slhv_conv.h>


smt_convt *create_new_z3_slhv_solver(
    const optionst &options,
    const namespacet &ns
) {
    z3_slhv_convt* conv = new z3_slhv_convt(ns, options);
    return conv;
}

z3_slhv_convt::z3_slhv_convt(const namespacet &_ns, const optionst& _options) : smt_convt(_ns, _options) {
    // initialize the z3 based slhv converter here
}