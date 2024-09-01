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

z3_slhv_convt::z3_slhv_convt(const namespacet &_ns, const optionst& _options)
  : z3_convt(_ns, _options) {
    // initialize the z3 based slhv converter here
    int_encoding = true;
    solver = z3::solver(z3_ctx, "SLHV");
    log_status("z3_slhv_convt created");
}

z3_slhv_convt::~z3_slhv_convt() { delete_all_asts(); }

smt_convt::resultt z3_slhv_convt::dec_solve() {
  log_status("z3-slhv debug: before slhv check");

  const std::string &path = options.get_option("output");
  if (path != "-")
  {
    std::ofstream out(path, std::ios_base::app);
    out << "SMT formulas for VCCs:\n";
    for(z3::expr expr : solver.assertions()) {
      out << expr.to_string() << '\n';
    }
    out.close();
  }

  z3::check_result result = solver.check();

  log_status("z3-slhv debug: after check");
  log_status("Dec result - {}",
    result == z3::sat ? "sat" :
      result == z3::unsat ? "unsat" :
        "error");

  if (result == z3::sat)
    return P_SATISFIABLE;

  if (result == z3::unsat)
    return smt_convt::P_UNSATISFIABLE;

  return smt_convt::P_ERROR;
}

const std::string z3_slhv_convt::solver_text() {
  return "Z3-slhv";
}

smt_astt z3_slhv_convt::mk_emp() {
  return new_ast(z3_ctx.emp_const(), this->mk_intheap_sort());
}
smt_astt z3_slhv_convt::mk_nil() {
  return new_ast(z3_ctx.nil_const(), this->mk_intloc_sort());
}
smt_astt z3_slhv_convt::mk_pt(smt_astt a, smt_astt b) {
  assert(a->sort == mk_intloc_sort());
  return new_ast(
    z3::points_to(
      to_solver_smt_ast<z3_smt_ast>(a)->a,
      to_solver_smt_ast<z3_smt_ast>(b)->a
    ),
    this->mk_intheap_sort());
}
smt_astt z3_slhv_convt::mk_uplus(smt_astt a, smt_astt b) {
  assert(a->sort == mk_intheap_sort());
  assert(b->sort == mk_intheap_sort());
  return new_ast(
    z3::uplus(
      to_solver_smt_ast<z3_smt_ast>(a)->a,
      to_solver_smt_ast<z3_smt_ast>(b)->a
    ),
    this->mk_intheap_sort());
}
smt_astt z3_slhv_convt::mk_uplus(std::vector<smt_astt> pts) {
  z3::expr_vector pt_vec(z3_ctx);
  for (auto pt : pts) {
    pt_vec.push_back(to_solver_smt_ast<z3_smt_ast>(pt)->a);
  }
  return new_ast(z3::uplus(pt_vec), this->mk_intheap_sort());
}
smt_astt z3_slhv_convt::mk_subh(smt_astt a, smt_astt b) {
  assert(a->sort == mk_intheap_sort());
  assert(b->sort == mk_intheap_sort());
  return new_ast(
    z3::subh(
      to_solver_smt_ast<z3_smt_ast>(a)->a,
      to_solver_smt_ast<z3_smt_ast>(b)->a
    ),
    this->boolean_sort);
}
smt_astt z3_slhv_convt::mk_disjh(smt_astt a, smt_astt b) {
  assert(a->sort == mk_intheap_sort());
  assert(b->sort == mk_intheap_sort());
  return new_ast(
    z3::disjh(
      to_solver_smt_ast<z3_smt_ast>(a)->a,
      to_solver_smt_ast<z3_smt_ast>(b)->a
    ),
    this->boolean_sort);
}
smt_astt z3_slhv_convt::mk_locadd(smt_astt a, smt_astt b) {
  assert(a->sort == mk_intloc_sort() || b->sort == mk_intloc_sort());
  return new_ast(
    z3::locadd(
      to_solver_smt_ast<z3_smt_ast>(a)->a,
      to_solver_smt_ast<z3_smt_ast>(b)->a
    ),
    this->mk_intloc_sort()
  );
}

BigInt z3_slhv_convt::get_bv(smt_astt a, bool is_signed){
  log_error("SLHV does not support bv");
  abort();
}

smt_sortt z3_slhv_convt::mk_intheap_sort() {
  return new solver_smt_sort<z3::sort>(SMT_SORT_INTHEAP, z3_ctx.intheap_sort());
}

smt_sortt z3_slhv_convt::mk_intloc_sort() {
  return new solver_smt_sort<z3::sort>(SMT_SORT_INTLOC, z3_ctx.intloc_sort());
}

smt_sortt z3_slhv_convt::mk_struct_sort(const type2tc &type) {
  return mk_intloc_sort();
}

smt_astt z3_slhv_convt::mk_smt_symbol(const std::string &name, smt_sortt s) {
  z3::expr e(z3_ctx);
  switch (s->id) {
    case SMT_SORT_INTHEAP:
      e = z3_ctx.hvar_const(name.c_str());
      break;
    case SMT_SORT_INTLOC:
      e = z3_ctx.locvar_const(name.c_str());
      break;
    default:
      e = z3_ctx.constant(name.c_str(), to_solver_smt_sort<z3::sort>(s)->s);
  }
  return new_ast(e, s);
}

smt_sortt z3_slhv_convt::convert_slhv_sorts(const type2tc &type) {
  switch (type->type_id) {
    case type2t::intheap_id: return mk_intheap_sort();
    case type2t::intloc_id: return mk_intloc_sort();
    default: {
      log_error("Unexpected type for SLHV");
      abort();
    }
  }
}

smt_astt
z3_slhv_convt::convert_slhv_opts(
  const expr2tc &expr, const std::vector<smt_astt>& args)
{
  switch (expr->expr_id)
  {
    case expr2t::constant_intheap_id:
      return mk_emp();
    case expr2t::constant_intloc_id:
      return mk_nil();
    case expr2t::heap_region_id:
    {
      const intheap_type2t &_type = to_intheap_type(expr->type);
      
      std::vector<smt_astt> pt_vec;
      if (_type.is_aligned)
      {
        for (unsigned i = 0; i < _type.field_types.size(); i++)
        {
          smt_astt loc = i == 0 ? args[1] : mk_locadd(args[1], mk_smt_int(BigInt(i)));
          smt_sortt sort =
            is_intloc_type(_type.field_types[i]) ?
              mk_intloc_sort() : mk_int_sort();
          std::string name =
            mk_fresh_name(
              is_intloc_type(_type.field_types[i]) ?
                "tmp_loc::" : "tmp_val::");
          smt_astt v = mk_fresh(sort, name);
          pt_vec.push_back(mk_pt(loc, v));
        }
      }
      else
      {
        // Default sort is intloc
        pt_vec.push_back(
          mk_pt(
            args[1],
            mk_fresh(mk_intloc_sort(), mk_fresh_name("tmp_loc::")
            )
          )
        );
      }
      return pt_vec.size() == 1 ? pt_vec[0] : mk_uplus(pt_vec);
    }
    case expr2t::location_of_id:
    {
      const location_of2t &locof = to_location_of2t(expr);
      const expr2tc &heap_region = locof.source_heap;
      const intheap_type2t &_type = to_intheap_type(heap_region->type);
      return convert_ast(_type.location);
    }
    case expr2t::points_to_id:
    {
      assert(args.size() == 2);
      return mk_pt(args[0], args[1]);
    }
    case expr2t::uplus_id:
    {
      assert(args.size() >= 2);
      smt_astt h = args[0];
      for (int i = 1; i < args.size(); i++) {
        h = mk_uplus(h, args[i]);
      }
      return h;
    }
    case expr2t::add_id:
    case expr2t::sub_id:
    case expr2t::locadd_id:
    {
      assert(args.size() == 2);
      return mk_locadd(args[0], args[1]);
    }
    case expr2t::heap_append_id:
    {
      const heap_append2t &heap_app = to_heap_append2t(expr);

      if (is_constant_intheap2t(heap_app.source_heap))
        return args[1];

      smt_astt h = args[0];
      smt_astt t = args[1];
      // new heap state
      return mk_uplus(h, t);
    }
    case expr2t::heap_contain_id:
    {
      const heap_contain2t& heap_ct = to_heap_contain2t(expr);
      const expr2tc &src_heap = heap_ct.source_heap;
      const expr2tc &heap_term = heap_ct.operand;
      if (!is_intheap_type(src_heap) || !is_intheap_type(heap_term))
      {
        log_error("Wrong heap term");
        abort();
      }
      return mk_subh(args[1], args[0]);
    }
    case expr2t::field_of_id:
    case expr2t::heap_update_id:
    case expr2t::heap_delete_id:
    {
      z3_slhv_convt::smt_ast_pair sap = convert_opt_without_assert(expr);
      assert_ast(sap.first);
      return sap.second;
    }
    case expr2t::same_object_id:
    {
      // Do project for SLHV
      const same_object2t& same = to_same_object2t(expr);
      z3_slhv_convt::smt_ast_pair p1 = this->project(same.side_1);
      z3_slhv_convt::smt_ast_pair p2 = this->project(same.side_2);
      
      smt_astt cond = mk_and(p1.first, p2.first);
      smt_astt eq = mk_eq(p1.second, p2.second);

      return mk_and(cond, eq);
    }
    default: {
      log_status("Invalid SLHV operations!!!");
      abort();
    }
  }
}

z3_slhv_convt::smt_ast_pair
z3_slhv_convt::convert_opt_without_assert(const expr2tc &expr)
{
  switch (expr->expr_id)
  {
    case expr2t::field_of_id:
    {
      const field_of2t &field_of = to_field_of2t(expr);

      if (is_constant_intheap2t(field_of.source_heap))
        return std::make_pair(
          mk_smt_bool(true),
          mk_fresh(convert_sort(field_of.type), mk_fresh_name("invalid_loc_")));

      if (!is_constant_int2t(field_of.operand))
      {
        log_error("Wrong field");
        abort();
      }

      const expr2tc &heap_region = field_of.source_heap;
      const intheap_type2t &_type = to_intheap_type(heap_region->type);
      const expr2tc &field = field_of.operand;
      unsigned int _field = to_constant_int2t(field).value.to_uint64();

      smt_astt source_loc = convert_ast(_type.location);
      smt_astt loc = _field == 0 ?
        source_loc : mk_locadd(source_loc, convert_ast(field));

      smt_sortt s1;
      std::string name;
      if (!_type.is_aligned)
      {
        s1 = mk_intloc_sort();
        name = mk_fresh_name("tmp_loc::");
      }
      else
      {
        s1 = is_intloc_type(_type.field_types[_field]) ? mk_intloc_sort() : mk_int_sort();
        name = mk_fresh_name(
          is_intloc_type(_type.field_types[_field]) ? "tmp_loc::" : "tmp_val::");
      }
      smt_astt v1 = mk_fresh(s1, name);

      smt_astt assert_expr = mk_subh(mk_pt(loc, v1), convert_ast(heap_region));
      return std::make_pair(assert_expr, v1);
    }
    case expr2t::heap_update_id:
    {
      const heap_update2t &heap_upd = to_heap_update2t(expr);
      if (!is_constant_int2t(heap_upd.operand_1))
      {
        log_error("Wrong field");
        abort();
      }

      const expr2tc &heap_region = heap_upd.source_heap;
      const intheap_type2t &_type = to_intheap_type(heap_region->type);
      const expr2tc &upd_field = heap_upd.operand_1;
      const expr2tc &upd_value = heap_upd.operand_2;

      unsigned int _field = to_constant_int2t(upd_field).value.to_uint64();

      smt_astt h = convert_ast(heap_region);
      smt_astt source_loc = convert_ast(_type.location);
      smt_astt field = convert_ast(upd_field);
      smt_astt loc = _field == 0 ? source_loc : mk_locadd(source_loc, field);
      smt_astt val = convert_ast(upd_value);

      smt_astt h1 = mk_fresh(mk_intheap_sort(), mk_fresh_name("tmp_heap::"));
      smt_astt v1 = mk_fresh(val->sort, mk_fresh_name("tmp_val::"));

      // current heap state
      smt_astt old_state = mk_uplus(h1, mk_pt(loc, v1));
      smt_astt assert_expr = mk_eq(h, old_state);

      // new heap state
      smt_astt new_state = mk_uplus(h1, mk_pt(loc, val));

      // new heap state
      return std::make_pair(assert_expr,  new_state);
    }
    case expr2t::heap_delete_id:
    {
      const heap_delete2t &heap_del = to_heap_delete2t(expr);

      smt_astt h = convert_ast(heap_del.source_heap);
      smt_astt l = convert_ast(heap_del.operand);

      smt_astt h1 = mk_fresh(mk_intheap_sort(), mk_fresh_name("tmp_heap::"));
      smt_astt v1 = mk_fresh(mk_int_sort(), mk_fresh_name("tmp_val::"));
      smt_astt assert_expr = mk_eq(h, mk_uplus(h1, mk_pt(l, v1)));
      
      return std::make_pair(assert_expr, h1);
    }
    default: {
      return std::make_pair(mk_smt_bool(true), convert_ast(expr));
    }
  }
}

z3_slhv_convt::smt_ast_pair
z3_slhv_convt::project(const expr2tc &expr)
{
  if (is_symbol2t(expr))
  {
    if (is_intheap_type(expr))
    {
      const intheap_type2t &_type = to_intheap_type(expr->type);
      return this->project(_type.location);
    }
    return convert_opt_without_assert(expr);
  }
  else if (is_location_of2t(expr))
    return this->project(to_location_of2t(expr).source_heap);
  else if (is_field_of2t(expr))
    return convert_opt_without_assert(expr);
  else if (is_typecast2t(expr))
    return this->project(to_typecast2t(expr).from);
  else if (is_locadd2t(expr) || is_add2t(expr) || is_sub2t(expr))
  {
    // TODO : fix
    expr2tc ptr;
    if (is_locadd2t(expr))
      ptr = to_locadd2t(expr).location;
    else if (is_add2t(expr))
      ptr = (is_pointer_type(to_add2t(expr).side_1) || is_intloc_type(to_add2t(expr).side_1))?
        to_add2t(expr).side_1 : to_add2t(expr).side_2;
    else if (is_sub2t(expr))
      ptr = (is_pointer_type(to_sub2t(expr).side_1) || is_intloc_type(to_sub2t(expr).side_1))?
        to_sub2t(expr).side_1 : to_sub2t(expr).side_2;
    return this->project(ptr);
 }
else
{
  log_error("Do not support project");
  expr->dump();
  abort();
}
}

void z3_slhv_convt::dump_smt() {
  const std::string &path = options.get_option("output");
  if(path == "-") {
    print_smt_formulae(std::cout);
  } else {
    std::ofstream out(path);
    print_smt_formulae(out);
  }
}

void z3_slhv_convt::print_smt_formulae(std::ostream& dest) {
  auto smt_formula = solver.to_smt2();
  std::replace(smt_formula.begin(), smt_formula.end(), '\\', '_');
  Z3_ast_vector __z3_assertions = Z3_solver_get_assertions(z3_ctx, solver);
  // Add whatever logic is needed.
  // Add solver specific declarations as well.
  dest << "(set-logic SLHV)" << std::endl;
  dest << "(set-info :smt-lib-version 2.6)\n";
  dest << "(set-option :produce-models true)\n";
  dest << "(declare-datatype pt_record_0 ((Pt_R_0 (loc IntLoc))))" << std::endl;
  dest << "(declare-datatype pt_record_1 ((Pt_R_1 (data Int))))" << std::endl;
  // dest << "(declare-fun emp () IntHeap)" << std::endl;
  // dest << "(declare-fun nil () IntLoc)" << std::endl;
  dest << "; Asserts from ESMBC starts\n";
  dest << smt_formula; // All VCC conditions in SMTLIB format.
  dest << "; Asserts from ESMBC ends\n";
  dest << "(get-model)\n";
  dest << "(exit)\n";
  log_status(
    "Total number of safety properties: {}",
    Z3_ast_vector_size(z3_ctx, __z3_assertions));
}