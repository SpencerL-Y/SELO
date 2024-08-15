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
  }

  z3::check_result result = solver.check();

  log_status("z3-slhv debug: after check");

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
  assert(is_intloc_type(type));
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
  const expr2tc &expr, const std::vector<smt_astt>& args) {
  switch (expr->expr_id) {
    case expr2t::constant_intheap_id: return mk_emp();
    case expr2t::constant_intloc_id: return mk_nil();
    case expr2t::heap_region_id:
    {
      log_status("convert heap region");
      assert(args.size() == 4);
      const heap_region2t& region = to_heap_region2t(expr);
      region.dump();
      assert(is_constant_int2t(region.size));
      const int n = to_constant_int2t(region.size).as_ulong();
      
      std::vector<smt_astt> pt_vec;
      for (unsigned i = 0; i < n; i++) {
        smt_astt loc = i == 0 ? args[1] : mk_locadd(args[1], mk_smt_int(BigInt(i)));
        smt_astt v = mk_fresh(mk_int_sort(), mk_fresh_name("tmp_val::"));
        pt_vec.push_back(mk_pt(loc, v));
      }
      return pt_vec.size() == 1 ? pt_vec[0] : mk_uplus(pt_vec);
    }
    case expr2t::pointer_with_region_id:
    {
      return convert_ast(to_pointer_with_region2t(expr).loc_ptr);
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
      const heap_append2t& heap_app = to_heap_append2t(expr);
      // TODO : fix width
      assert(heap_app.byte_len == 4);
      smt_astt h = args[0];
      smt_astt adr = args[1];
      smt_astt val = args[2];
      // new heap state
      return mk_uplus(h, mk_pt(adr, val));
    }
    case expr2t::heap_update_id:
    {
      const heap_update2t& heap_upd = to_heap_update2t(expr);
      // TODO : fix width
      assert(heap_upd.byte_len == 4);
      smt_astt h = args[0];
      smt_astt h1 = mk_fresh(mk_intheap_sort(), mk_fresh_name("tmp_heap::"));
      smt_astt adr = args[1];
      smt_astt val = args[2];
      smt_astt v1 = mk_fresh(val->sort, mk_fresh_name("tmp_val::"));
      // current heap state
      smt_astt o_state = mk_eq(h, mk_uplus(mk_pt(adr, v1), h1));
      assert_ast(o_state);
      // new heap state
      return mk_uplus(mk_pt(adr, val), h1);
    }
    case expr2t::heap_load_id:
    {
      const heap_load2t& heap_load = to_heap_load2t(expr);
      // TODO : fix width
      // assert(heap_load.byte_len == 4);
      //current heap state
      assert_ast(mk_subh(mk_pt(args[2], args[0]), args[1]));
      return args[0];
    }
    case expr2t::heap_contains_id:
    {
      const heap_contains2t& heap_ct = to_heap_contains2t(expr);
      // TODO : fix width
      // assert(heap_ct.byte_len == 4);
      smt_astt sh;
      if (is_symbol2t(heap_ct.hterm) ||
          is_pointer_with_region2t(heap_ct.hterm) ||
          is_pointer_object2t(heap_ct.hterm))
      {
        sh = mk_pt(args[0], mk_fresh(mk_int_sort(), mk_fresh_name("tmp_val::")));
        // TODO : support multiple loaded
      }
      else if (is_points_to2t(heap_ct.hterm))
      {
        sh = args[0];
      }
      return mk_subh(sh, args[1]);
    }
    case expr2t::heap_delete_id:
    {
      smt_astt h1 = mk_fresh(mk_intheap_sort(), mk_fresh_name("tmp_heap::"));
      smt_astt v1 = mk_fresh(mk_int_sort(), mk_fresh_name("tmp_val::"));
      assert_ast(mk_eq(args[0], mk_uplus(h1, mk_pt(args[1], v1))));
      return h1;
    }
    case expr2t::same_object_id:
    {
      // Do project for SLHV
      const same_object2t& same = to_same_object2t(expr);
      smt_astt p1 = this->project(same.side_1);
      smt_astt p2 = this->project(same.side_2);
      return mk_eq(p1, p2);
    }
    default: {
      log_status("Invalid SLHV operations!!!");
      abort();
    }
  }
}

smt_astt z3_slhv_convt::project(const expr2tc &expr)
{
  if (is_constant_intheap2t(expr) || is_constant_intloc2t(expr))
    return convert_ast(expr);
  else if (is_pointer_with_region2t(expr))
    return convert_ast(expr);
  else if (is_heap_region2t(expr))
    return convert_ast(to_heap_region2t(expr).start_loc);
  else if (is_heap_load2t(expr))
    return convert_ast(to_heap_load2t(expr).flag);
  else if (is_typecast2t(expr))
    return this->project(to_typecast2t(expr).from);
  else if (is_locadd2t(expr) || is_add2t(expr) || is_sub2t(expr))
  {
    expr2tc ptr;
    if (is_locadd2t(expr))
      ptr = to_locadd2t(expr).loc;
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