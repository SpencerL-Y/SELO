#include <cassert>
#include <iostream>
#include <solvers/smt/smt_conv.h>
#include <z3_slhv_conv.h>

#define new_ast new_solver_ast<z3_smt_ast>

smt_convt *create_new_z3_slhv_solver(
  const optionst &options,
  const namespacet &ns,
  tuple_iface **tuple_api,
  array_iface **array_api,
  fp_convt **fp_api)
{
  std::string z3_file = options.get_option("z3-debug-dump-file");
  if (options.get_bool_option("z3-debug"))
  {
    // Generate Z3 API file
    Z3_open_log(z3_file.empty() ? "z3.log" : z3_file.c_str());

    // Add Type checker
    z3::config().set("stats", "true");

    // Add typecheck
    z3::config().set("type_check", "true");
    z3::config().set("well_sorted_check", "true");

    // SMT2 Compliant
    z3::config().set("smtlib2_compliant", "true");
  }

  if (
    options.get_bool_option("--smt-formula-only") ||
    options.get_bool_option("--smt-formula-too"))
    z3::config().set("smtlib2_compliant", "true");

  z3_slhv_convt *conv = new z3_slhv_convt(ns, options);
  *tuple_api = static_cast<tuple_iface *>(conv);
  *array_api = static_cast<array_iface *>(conv);
  *fp_api = static_cast<fp_convt *>(conv);
  log_status("z3_slhv solver created");
  return conv;
}

// smt_astt z3_slhv_smt_ast::update(smt_convt *ctx,
//   smt_astt value,
//   unsigned int idx,
//   expr2tc idx_expr)
//   const {
//     log_status("slhv_smt does not support update");
//     return nullptr;
//   }
// smt_astt z3_slhv_smt_ast::project(smt_convt *ctx, unsigned int elem) const  {
//   log_status("slhv_smt does not support project");
//   return nullptr;
// }
// void z3_slhv_smt_ast::dump() const  {
//   std::string print_str = a.to_string();
//   log_status("{}\n sort is {}", print_str, a.get_sort().to_string());
// }

z3_slhv_convt::z3_slhv_convt(const namespacet &_ns, const optionst& _options) : z3_convt(_ns, _options) {
    // initialize the z3 based slhv converter here
    int_encoding = true;
    log_status("z3_slhv_convt created");
}

z3_slhv_convt::~z3_slhv_convt() { delete_all_asts(); }

// void z3_slhv_convt::push_ctx() {

// }

// void z3_slhv_convt::pop_ctx() {

// }

void z3_slhv_convt::assert_ast(smt_astt a) {
  this->assertions.push_back(a);
}

smt_convt::resultt z3_slhv_convt::dec_solve() {
  return P_SMTLIB;
}

const std::string z3_slhv_convt::solver_text() {
  return "Z3-slhv";
}

// smt_astt z3_slhv_convt::mk_smt_int(const BigInt &theint) {
//   smt_sortt s = mk_int_sort();
//   if (theint.is_negative())
//     return new_ast(z3_ctx.int_val(theint.to_int64()), s);

//   return new_ast(z3_ctx.int_val(theint.to_uint64()), s);
// }

// smt_astt z3_slhv_convt::mk_smt_real(const std::string &str) {
//   log_error("SLHV does not support real yet");
//   abort();
//   return nullptr;
// }

// smt_astt z3_slhv_convt::mk_smt_bv(const BigInt &theint, smt_sortt s) {
//   log_error("SLHV does not support bv");
//   abort();
//   return nullptr;
// }
// smt_astt z3_slhv_convt::mk_smt_bool(bool val){
//   return new_ast(z3_ctx.bool_val(val), mk_bool_sort());
// }

// smt_astt z3_slhv_convt::mk_smt_symbol(const std::string &name, smt_sortt s){
//   switch (s->id)
//   {
//   case SMT_SORT_BOOL: {
//     z3::expr bexpr = this->z3_ctx.bool_const(name.c_str());
//     return new_ast(bexpr, s);
//   }
//   case SMT_SORT_INT: {
//     z3::expr ivar = this->z3_ctx.int_const(name.c_str());
//     return new_ast(ivar, s);
//   }
//   case SMT_SORT_INTHEAP: {
//     z3::expr hvar_expr = this->z3_ctx.hvar_const(name.c_str());
//     return new_ast(hvar_expr, s);
//   }
//   case SMT_SORT_INTLOC: {
//     z3::expr lvar_expr = this->z3_ctx.locvar_const(name.c_str());
//     return new_ast(lvar_expr, s);
//   }
//   default:
//     log_status("unsupported sort in symbol making");
//     break;
//   }
// }
// smt_astt z3_slhv_convt::mk_extract(smt_astt a, unsigned int high, unsigned int low){
//   log_error("SLHV does not support bv");
//   abort();
  
// }
// smt_astt z3_slhv_convt::mk_sign_ext(smt_astt a, unsigned int topwidth){
  
//   log_error("SLHV does not support bv");
//   abort();
// }
// smt_astt z3_slhv_convt::mk_zero_ext(smt_astt a, unsigned int topwidth){
  
//   log_error("SLHV does not support bv");
//   abort();
// }
// smt_astt z3_slhv_convt::mk_concat(smt_astt a, smt_astt b){
//   log_error("SLHV does not support bv");
//   abort();
// }
// // logical connections
// smt_astt z3_slhv_convt::mk_ite(smt_astt cond, smt_astt t, smt_astt f){
  
// }

// smt_astt z3_slhv_convt::mk_or(smt_astt a, smt_astt b) {}
// smt_astt z3_slhv_convt::mk_and(smt_astt a, smt_astt b) {}
// smt_astt z3_slhv_convt::mk_implies(smt_astt a, smt_astt b) {
//   z3::expr premise = to_solver_smt_ast<z3_slhv_smt_ast>(a)->a;
//   z3::expr conclusion = to_solver_smt_ast<z3_slhv_smt_ast>(b)->a;
//   z3::expr impl = z3::implies(premise, conclusion);
//   return new_ast(impl, boolean_sort);
// }
// smt_astt z3_slhv_convt::mk_not(smt_astt a) {
//   z3::expr noteq = !to_solver_smt_ast<z3_slhv_smt_ast>(a)->a;
//   return new_ast(noteq, boolean_sort);
// }
// // numeral assertions
// smt_astt z3_slhv_convt::mk_lt(smt_astt a, smt_astt b) {}
// smt_astt z3_slhv_convt::mk_le(smt_astt a, smt_astt b) {}
// smt_astt z3_slhv_convt::mk_gt(smt_astt a, smt_astt b) {}
// smt_astt z3_slhv_convt::mk_ge(smt_astt a, smt_astt b) {}
// smt_astt z3_slhv_convt::mk_eq(smt_astt a, smt_astt b) {
//     assert(a->sort->id == b->sort->id);
//     z3::expr lhs = to_solver_smt_ast<z3_slhv_smt_ast>(a)->a;
//     z3::expr rhs = to_solver_smt_ast<z3_slhv_smt_ast>(b)->a;
//     z3::expr z3eq = (lhs == rhs);
//     return new_ast(z3eq, boolean_sort);
// }
// smt_astt z3_slhv_convt::mk_neq(smt_astt a, smt_astt b) {}
// // numeral terms
// smt_astt z3_slhv_convt::mk_add(smt_astt a, smt_astt b) {

// }

// heap terms
smt_astt z3_slhv_convt::mk_pt(smt_astt a, smt_astt b) {
  z3::expr pt = z3::points_to(
    to_solver_smt_ast<z3_smt_ast>(a)->a,
    to_solver_smt_ast<z3_smt_ast>(b)->a
  );
  return new_ast(pt, this->mk_intheap_sort());
}
smt_astt z3_slhv_convt::mk_uplus(smt_astt a, smt_astt b){
  z3::expr h = z3::uplus(
    to_solver_smt_ast<z3_smt_ast>(a)->a,
    to_solver_smt_ast<z3_smt_ast>(b)->a
  );
  return new_ast(h, this->mk_intheap_sort());
}
smt_astt z3_slhv_convt::mk_emp() {
  z3::expr emp = z3_ctx.emp_const();
  return new_ast(emp, this->mk_intheap_sort());
}
// loc terms
smt_astt z3_slhv_convt::mk_locadd(smt_astt loc, smt_astt i) {

}
smt_astt z3_slhv_convt::mk_nil() {
  z3::expr nil = z3_ctx.nil_const();
  return new_ast(nil, this->mk_intloc_sort());
}

bool z3_slhv_convt::get_bool(smt_astt a){
  log_error("Can't get boolean value yet, solver not plugged.");
  abort();
}
BigInt z3_slhv_convt::get_bv(smt_astt a, bool is_signed){
  log_error("SLHV does not support bv");
  abort();
}

// smt_sortt z3_slhv_convt::mk_bool_sort() {
//   return new solver_smt_sort<z3::sort>(SMT_SORT_BOOL, z3_ctx.bool_sort());
// }

// smt_sortt z3_slhv_convt::mk_int_sort() {
//   return new solver_smt_sort<z3::sort>(SMT_SORT_INT, z3_ctx.int_sort());
// }

smt_sortt z3_slhv_convt::mk_intheap_sort() {
  return new solver_smt_sort<z3::sort>(SMT_SORT_INTHEAP, z3_ctx.intheap_sort());
}

smt_sortt z3_slhv_convt::mk_intloc_sort() {
  return new solver_smt_sort<z3::sort>(SMT_SORT_INTLOC, z3_ctx.intloc_sort());
}

smt_sortt z3_slhv_convt::mk_struct_sort(const type2tc &type) {
  assert(is_intloc_type(type));
  return mk_intloc_sort();
}

// smt_astt z3_slhv_convt::convert_ast_slhv(const expr2tc &expr) {
//   log_status("== convert ast slhv");
//   expr->dump();
//   log_status("====");
//   smt_cachet::const_iterator cache_result = smt_cache.find(expr);
//   if (cache_result != smt_cache.end()) {
//     log_status("found -------------------::");
//     expr->dump();
//     return (cache_result->ast);
//   }

//   if (is_vector_type(expr)) {
//     log_status("WARNING!!!: does not support convert ast slhv vector type");
//   }

//   std::vector<smt_astt> args;
//   args.reserve(expr->get_num_sub_exprs());

//   switch(expr->expr_id) {

//   case expr2t::with_id:
//   case expr2t::constant_array_id:
//   case expr2t::constant_vector_id:
//   case expr2t::constant_array_of_id:
//   case expr2t::index_id:
//   case expr2t::address_of_id:
//   case expr2t::ieee_add_id:
//   case expr2t::ieee_sub_id:
//   case expr2t::ieee_mul_id:
//   case expr2t::ieee_div_id:
//   case expr2t::ieee_fma_id:
//   case expr2t::ieee_sqrt_id:
//   case expr2t::pointer_offset_id:
//   case expr2t::pointer_object_id:
//   case expr2t::pointer_capability_id:
//     break; // Don't convert their operands

//   default:
//   {
//     // Convert all the arguments and store them in 'args'.
//     unsigned int i = 0;
//     expr->foreach_operand(
//       [this, &args, &i](const expr2tc &e) { args[i++] = convert_ast_slhv(e); });
//   }
//   }

//   log_status(" ------------- covert args ends ------------- ");
//   expr->dump();

//   smt_astt a;
//   switch (expr->expr_id)
//   {

//   case expr2t::constant_intheap_id: {
//     const constant_intheap2t& intheap = to_constant_intheap2t(expr);
//     log_status("{}", intheap.is_emp);
//     expr->dump();
//     if (intheap.is_emp) {
//       a = mk_emp();
//     } else {
      
//     }
//     break;
//   }
//   case expr2t::constant_intloc_id: {
//     const constant_intloc2t& intloc = to_constant_intloc2t(expr);
//     if (intloc.value.is_zero()) {
//       a = mk_nil();
//     } else {

//     }
//     break;
//   }
//   case expr2t::points_to_id: {
//     assert(args.size() == 2);
//     a = mk_pt(args[0], args[1]);
//     break;
//   }
//   case expr2t::uplus_id: {
//     assert(args.size() >= 2);
//     a = args[0];
//     for (int i = 1; i < args.size(); i++) {
//       a = mk_uplus(a, args[i]);
//     }
//     break;
//   }
//   case expr2t::locadd_id: {
//     assert(args.size() == 2);
//     a = mk_locadd(args[0], args[1]);
//     break;
//   }
//   case expr2t::constant_fixedbv_id:
//   case expr2t::constant_floatbv_id:
//   case expr2t::constant_string_id:
//   {
//     log_status("WARNING!!!: not supported expr id");
//     std::cout << expr->expr_id << std::endl;
//     break;
//   }
//   case expr2t::constant_int_id:
//   {
//     const constant_int2t &theint = to_constant_int2t(expr);
//     a = mk_smt_int(theint.value);
//     break;
//   }
//   case expr2t::constant_bool_id:
//   {
//     const constant_bool2t &thebool = to_constant_bool2t(expr);
//     a = mk_smt_bool(thebool.value);
//     break;
//   }
//   case expr2t::symbol_id:
//   {
//     const symbol2t &sym = to_symbol2t(expr);
//     std::string name = sym.get_symbol_name();
//     smt_sortt sort = convert_sort_slhv(sym.type);
//     std::cout << "symbol name: "  << name << std::endl;
//     std::cout << "symbol thename: " << sym.thename << std::endl;
//     std::cout << "sort name: " <<  sort->id << std::endl;
//     a = mk_smt_symbol(name, sort);
//     break;
//   }
//   case expr2t::constant_vector_id:
//   {
//     log_status("WARNING!!!: not supported constant vector id convert ast");
//     std::cout << expr->expr_id << std::endl;
//     break;
//   }

//   case expr2t::constant_array_id:
//   {
//     log_status("WARNING: constant array id encountered");
//     break;
//   }
//   case expr2t::constant_array_of_id:
//   {
//     const array_type2t &arr = to_array_type(expr->type);
//     const constant_array_of2t &aof_expr = to_constant_array_of2t(expr);
//     const expr2tc& init = aof_expr.initializer;
//     std::cout << "array of argument type id: " <<  init->type->type_id << std::endl;
//     if(is_constant_number(init)) {
//       a = this->mk_emp();
//     } else {
//       log_status("WARNING: initializer of array of not supported");
//     }

//     break;
//   }
//   case expr2t::add_id:
//   {
//     const add2t &add = to_add2t(expr);
//     if (
//       is_pointer_type(expr->type) || is_pointer_type(add.side_1) ||
//       is_pointer_type(add.side_2))
//     {
//       log_status("TODO: ptr adding not impled yet");
//     }
//     else  
//     {
//       a = mk_add(args[0], args[1]);
//     }
//   }
//   case expr2t::sub_id:
//   {
//     const sub2t &sub = to_sub2t(expr);
//     if (
//       is_pointer_type(expr->type) || is_pointer_type(sub.side_1) ||
//       is_pointer_type(sub.side_2))
//     {
//       log_status("TODO: ptr sub not impled yet");
//     }
//     else 
//     {
//       a = mk_sub(args[0], args[1]);
//     }
//     break;
//   }
//   case expr2t::mul_id:
//   {
//     log_status("WARNING: mul_id not supported");
//     break;
//   }
//   case expr2t::div_id:
//   {
//     log_status("WARNING: div_id not supported");
//     break;
//   }
//   case expr2t::ieee_add_id:
//   case expr2t::ieee_sub_id:
//   case expr2t::ieee_mul_id:
//   case expr2t::ieee_div_id:
//   case expr2t::ieee_fma_id:
//   case expr2t::ieee_sqrt_id:
//   {
    
//     log_status("WARNING: ieee expr2t not supported");
//     break;
//   }
//   case expr2t::modulus_id:
//   {
//     log_status("WARNING: modulus_id not supported");
//     break;
//   }
//   case expr2t::index_id:
//   {
//     log_status("TODO: index id not impled yet");
//     break;
//   }
//   case expr2t::with_id:
//   {
//     const with2t &with = to_with2t(expr);
//     log_status("TODO: with id not impled yet");
//     // We reach here if we're with'ing a struct, not an array. Or a bool.
//     if (is_struct_type(expr) || is_pointer_type(expr))
//     {
//       log_status("expr struct/ptr type");
//     }
//     else if (is_union_type(expr))
//     {
//       log_status("expr union type");
//     }
//     else
//     {
//       log_status("expr other type");
//     }
//     break;
//   }
//   case expr2t::member_id:
//   {
//     log_status("TODO: member_id not impled yet");
//     break;
//   }
//   case expr2t::same_object_id:
//   {
//     log_status("TODO: same_object_id not impled yet");
//     break;
//   }
//   case expr2t::pointer_offset_id:
//   {
//     log_status("TODO: pointer_offset_id not impled yet");
//     break;
//   }
//   case expr2t::pointer_object_id:
//   {
//     log_status("TODO: pointer_object_id not impled yet");
//     break;
//   }
//   case expr2t::pointer_capability_id:
//   {
//     log_status("TODO: pointer_capability_id not impled yet");
//     break;
//   }
//   case expr2t::typecast_id:
//   {
//     log_status("TODO: typecast_id not impled yet");
//     break;
//   }
//   case expr2t::nearbyint_id:
//   {
//     log_status("WARNING: nearbyint_id not supported");
//     break;
//   }
//   case expr2t::if_id:
//   {
//     // Only attempt to handle struct.s
//     const if2t &if_ref = to_if2t(expr);
//     args[0] = convert_ast(if_ref.cond);
//     args[1] = convert_ast(if_ref.true_value);
//     args[2] = convert_ast(if_ref.false_value);
//     a = args[1]->ite(this, args[0], args[2]);
//     break;
//   }
//   case expr2t::isnan_id:
//   {
//     log_status("WARNING: isnan_id not supported");
//     break;
//   }
//   case expr2t::isinf_id:
//   {
//     log_status("WARNING: isinf_id not supported");
//     break;
//   }
//   case expr2t::isnormal_id:
//   {
//     log_status("WARNING: isnormal_id not supported");
//     break;
//   }
//   case expr2t::isfinite_id:
//   {
//     log_status("WARNING: isfinite_id not supported");
//     break;
//   }
//   case expr2t::signbit_id:
//   {
//     log_status("WARNING: signbit_id not supported");
//     break;
//   }
//   case expr2t::popcount_id:
//   {
//     log_status("WARNING: popcount_id not supported");
//     break;
//   }
//   case expr2t::bswap_id:
//   {
//     log_status("WARNING: bswap_id not supported");
//     break;
//   }
//   case expr2t::overflow_id:
//   {
//     log_status("WARNING: overflow_id not supported");
//     break;
//   }
//   case expr2t::overflow_cast_id:
//   {
//     log_status("WARNING: overflow_cast_id not supported");
//     break;
//   }
//   case expr2t::overflow_neg_id:
//   {
//     log_status("WARNING: overflow_neg_id not supported");
//     break;
//   }
//   case expr2t::byte_extract_id:
//   {
//     log_status("WARNING: byte_extract_id not supported");
//     break;
//   }
//   case expr2t::byte_update_id:
//   {
//     log_status("WARNING: byte_update_id not supported");
//     break;
//   }
//   case expr2t::address_of_id:
//   {
//     log_status("WARNING: address_of_id not supported");
//     break;
//   }
//   case expr2t::equality_id:
//   {
//     a = args[0]->eq(this, args[1]);
//     break;
//   }
//   case expr2t::notequal_id:
//   {
//     auto neq = to_notequal2t(expr);
//     a = args[0]->eq(this, args[1]);
//     a = mk_not(a);
//     break;
//   }
//   case expr2t::shl_id:
//   {
//     log_status("WARNING: shl_id not supported");
//     break;
//   }
//   case expr2t::ashr_id:
//   {
//     log_status("WARNING: ashr_id not supported");
//     break;
//   }
//   case expr2t::lshr_id:
//   {
//     log_status("WARNING: lshr_id not supported");
//     break;
//   }
//   case expr2t::abs_id:
//   {
//     log_status("WARNING: abs_id not supported");
//     break;
//   }
//   case expr2t::lessthan_id:
//   {
//     log_status("TODO: lessthan_id not impled yet");
//     break;
//   }
//   case expr2t::lessthanequal_id:
//   {
//     log_status("TODO: lessthanequal_id not impled yet");
//     break;
//   }
//   case expr2t::greaterthan_id:
//   {
//     log_status("TODO: greaterthan_id not impled yet");
//     break;
//   }
//   case expr2t::greaterthanequal_id:
//   {
    
//     log_status("TODO: greaterthanequal_id not impled yet");
//     break;
//   }
//   case expr2t::concat_id:
//   {
//     log_status("WARNING: concat_id not supported");
//     break;
//   }
//   case expr2t::implies_id:
//   {
//     a = mk_implies(args[0], args[1]);
//     break;
//   }
//   case expr2t::bitand_id:
//   case expr2t::bitor_id:
//   case expr2t::bitxor_id:
//   case expr2t::bitnand_id:
//   case expr2t::bitnor_id:
//   case expr2t::bitnxor_id:
//   case expr2t::bitnot_id:
//   {
//     log_status("WARNING: bit operations not supported");
//     break;
//   }
//   case expr2t::not_id:
//   {
//     assert(is_bool_type(expr));
//     a = mk_not(args[0]);
//     break;
//   }
//   case expr2t::neg_id:
//   {
//     const neg2t &neg = to_neg2t(expr);
//     a = mk_neg(args[0]);
//     break;
//   }
//   case expr2t::and_id:
//   {
//     a = mk_and(args[0], args[1]);
//     break;
//   }
//   case expr2t::or_id:
//   {
//     a = mk_or(args[0], args[1]);
//     break;
//   }
//   case expr2t::xor_id:
//   {
//     a = mk_xor(args[0], args[1]);
//     break;
//   }
//   case expr2t::bitcast_id:
//   {
//     log_status("WARNING: bitcast_id not supported");
//     break;
//   }
//   case expr2t::extract_id:
//   {
//     log_status("WARNING: extract_id not supported");
//     break;
//   }
//   case expr2t::code_comma_id:
//   {
//     log_status("WARNING: code_comma_id not supported");
//     break;
//   }
//   default:
//     log_error("Couldn't convert expression in unrecognised format\n{}", *expr);
//     abort();
//   }

//   struct smt_cache_entryt entry = {expr, a, ctx_level};
//   smt_cache.insert(entry);

//   log_status("==== converted reuslt: ");
//   a->dump();
//   log_status("====");
//   return a;
// }

// smt_sortt z3_slhv_convt::convert_sort_slhv(const type2tc &type) {
//   std::cout << "convert sort slhv, type name: " << type->type_id << std::endl;
//   smt_sort_cachet::const_iterator it = sort_cache.find(type);
//   if (it != sort_cache.end())
//   {
//     return it->second;
//   }

//   smt_sortt result = nullptr;
//   switch (type->type_id)
//   {
//   case type2t::bool_id:
//     result = boolean_sort;
//     break;

//   case type2t::struct_id:
//   {
//     log_status("INFO: convert struct_id sort");
    
//     break;
//   }
//   case type2t::code_id:
//   case type2t::pointer_id:
//     log_status("TODO: convert  code pointer id sort");
//     result = this->mk_intloc_sort();
//     break;


//   case type2t::intheap_id:
//   case type2t::array_id:
//   {
//     log_status("INFO: convert array id type  to intheap sort");
//     result = this->mk_intheap_sort();

//     break;
//   }
//   case type2t::signedbv_id:
//   {
//     result = this->mk_int_sort();
//     break;
//   }

//   default:
//     log_error(
//       "Unexpected type ID {} reached SMT conversion", get_type_id(type));
//     abort();
//   }

//   sort_cache.insert(smt_sort_cachet::value_type(type, result));
//   return result;
// }

// smt_astt z3_slhv_convt::convert_assign_slhv(const expr2tc &expr) {
//   const equality2t &eq = to_equality2t(expr);
//   smt_astt side1 = convert_ast_slhv(eq.side_1); // LHS
//   smt_astt side2 = convert_ast_slhv(eq.side_2); // RHS
//   side2->assign(this, side1);

//   smt_cache_entryt e = {eq.side_1, side2, ctx_level};
//   smt_cache.insert(e);
//   return side2;
// }


// void z3_slhv_convt::print_smt_formulae(std::ostream &dest) {
//   log_status("TODO: slhv print smt");
// }

// void z3_slhv_convt::dump_smt() {
//   log_status("TODO: slhv dump smt");
// }