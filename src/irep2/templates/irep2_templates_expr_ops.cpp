/**
 * @author Term SELO
 * @brief Modified by from ESBMC
 */

#include <irep2/irep2_templates_expr.h>

expr_typedefs1(not, bool_1op);
expr_typedefs2(and, logic_2ops);
expr_typedefs2(or, logic_2ops);
expr_typedefs2(xor, logic_2ops);
expr_typedefs2(implies, logic_2ops);
expr_typedefs2(bitand, bit_2ops);
expr_typedefs2(bitor, bit_2ops);
expr_typedefs2(bitxor, bit_2ops);
expr_typedefs2(bitnand, bit_2ops);
expr_typedefs2(bitnor, bit_2ops);
expr_typedefs2(bitnxor, bit_2ops);
expr_typedefs2(lshr, bit_2ops);
expr_typedefs1(bitnot, bitnot_data);
expr_typedefs1(neg, arith_1op);
expr_typedefs1(abs, arith_1op);
expr_typedefs2(add, arith_2ops);
expr_typedefs2(sub, arith_2ops);
expr_typedefs2(mul, arith_2ops);
expr_typedefs2(div, arith_2ops);
expr_typedefs3(ieee_add, ieee_arith_2ops);
expr_typedefs3(ieee_sub, ieee_arith_2ops);
expr_typedefs3(ieee_mul, ieee_arith_2ops);
expr_typedefs3(ieee_div, ieee_arith_2ops);
expr_typedefs4(ieee_fma, ieee_arith_3ops);
expr_typedefs2(ieee_sqrt, ieee_arith_1op);
expr_typedefs2(modulus, arith_2ops);
expr_typedefs2(shl, bit_2ops);
expr_typedefs2(ashr, bit_2ops);
expr_typedefs1(pointer_offset, pointer_ops);
expr_typedefs1(pointer_object, pointer_ops);
expr_typedefs1(pointer_capability, pointer_ops);
expr_typedefs1(address_of, pointer_ops);
expr_typedefs1(overflow, overflow_ops);
expr_typedefs1(valid_object, object_ops);
expr_typedefs1(dynamic_size, object_ops);
expr_typedefs1(deallocated_obj, object_ops);
expr_typedefs1(invalid_pointer, invalid_pointer_ops);
expr_typedefs1(isinf, bool_1op);
expr_typedefs1(isnormal, bool_1op);
expr_typedefs1(isfinite, bool_1op);
expr_typedefs1(signbit, overflow_ops);
expr_typedefs1(popcount, overflow_ops);
expr_typedefs1(bswap, arith_1op);
expr_typedefs2(concat, bit_2ops);
expr_typedefs1(isnan, bool_1op);
expr_typedefs1(overflow_neg, overflow_ops);

expr_typedefs1(location_of, heap_ops);
expr_typedefs3(field_of, heap_1op);
expr_typedefs4(heap_update, heap_2ops);
expr_typedefs2(heap_append, heap_1op);
expr_typedefs2(heap_delete, heap_1op);
expr_typedefs2(heap_contain, heap_1op);