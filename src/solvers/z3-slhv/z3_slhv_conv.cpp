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
  return conv;
}

z3_slhv_convt::z3_slhv_convt(const namespacet &_ns, const optionst& _options)
  : z3_convt(_ns, _options)
{
  // initialize the z3 based slhv converter here
  int_encoding = true;
  solver = z3::solver(z3_ctx, "SLHV");
}

z3_slhv_convt::~z3_slhv_convt() { delete_all_asts(); }

smt_convt::resultt z3_slhv_convt::dec_solve()
{
  const std::string &path = options.get_option("output");
  if (options.get_bool_option("show-vcc") && path != "-")
  {
    std::ofstream out(path, std::ios_base::app);
    out << "SMT formulas for VCCs:\n";
    for(z3::expr expr : solver.assertions()) {
      out << expr.to_string() << '\n';
    }
    out.close();
  }

  z3::check_result result = solver.check();

  if (result == z3::sat)
    return P_SATISFIABLE;

  if (result == z3::unsat)
    return smt_convt::P_UNSATISFIABLE;

  return smt_convt::P_ERROR;
}

const std::string z3_slhv_convt::solver_text() { return "Z3-slhv"; }

smt_sortt z3_slhv_convt::mk_intheap_sort()
{
  return new solver_smt_sort<z3::sort>(SMT_SORT_INTHEAP, z3_ctx.intheap_sort());
}

smt_sortt z3_slhv_convt::mk_intloc_sort()
{
  return new solver_smt_sort<z3::sort>(SMT_SORT_INTLOC, z3_ctx.intloc_sort());
}

smt_sortt z3_slhv_convt::mk_struct_sort(const type2tc &type)
{
  return mk_intloc_sort();
}

smt_astt z3_slhv_convt::mk_emp()
{
  return new_ast(z3_ctx.emp_const(), this->mk_intheap_sort());
}
smt_astt z3_slhv_convt::mk_nil()
{
  return new_ast(z3_ctx.nil_const(), this->mk_intloc_sort());
}
smt_astt z3_slhv_convt::mk_pt(smt_astt l, smt_astt v)
{
  assert(l->sort->id == SMT_SORT_INTLOC);
  return new_ast(
    z3::points_to(
      to_solver_smt_ast<z3_smt_ast>(l)->a,
      to_solver_smt_ast<z3_smt_ast>(v)->a
    ),
    this->mk_intheap_sort());
}
smt_astt z3_slhv_convt::mk_uplus(smt_astt ht1, smt_astt ht2)
{
  assert(ht1->sort->id == SMT_SORT_INTHEAP);
  assert(ht2->sort->id == SMT_SORT_INTHEAP);
  return new_ast(
    z3::uplus(
      to_solver_smt_ast<z3_smt_ast>(ht1)->a,
      to_solver_smt_ast<z3_smt_ast>(ht2)->a
    ),
    this->mk_intheap_sort());
}
smt_astt z3_slhv_convt::mk_uplus(std::vector<smt_astt> hts)
{
  z3::expr_vector ht_vec(z3_ctx);
  for (auto ht : hts) {
    ht_vec.push_back(to_solver_smt_ast<z3_smt_ast>(ht)->a);
  }
  return new_ast(z3::uplus(ht_vec), this->mk_intheap_sort());
}
smt_astt z3_slhv_convt::mk_subh(smt_astt ht1, smt_astt ht2)
{
  assert(ht1->sort->id == SMT_SORT_INTHEAP);
  assert(ht2->sort->id == SMT_SORT_INTHEAP);
  return new_ast(
    z3::subh(
      to_solver_smt_ast<z3_smt_ast>(ht1)->a,
      to_solver_smt_ast<z3_smt_ast>(ht2)->a
    ),
    this->boolean_sort);
}
smt_astt z3_slhv_convt::mk_disjh(smt_astt ht1, smt_astt ht2)
{
  assert(ht1->sort->id == SMT_SORT_INTHEAP);
  assert(ht2->sort->id == SMT_SORT_INTHEAP);
  return new_ast(
    z3::disjh(
      to_solver_smt_ast<z3_smt_ast>(ht1)->a,
      to_solver_smt_ast<z3_smt_ast>(ht2)->a
    ),
    this->boolean_sort);
}
smt_astt z3_slhv_convt::mk_locadd(smt_astt l, smt_astt o)
{
  assert(l->sort->id == SMT_SORT_INTLOC);
  return new_ast(
    z3::locadd(
      to_solver_smt_ast<z3_smt_ast>(l)->a,
      to_solver_smt_ast<z3_smt_ast>(o)->a
    ),
    this->mk_intloc_sort()
  );
}

smt_astt z3_slhv_convt::mk_loc2int(smt_astt l)
{
  assert(l->sort->id == SMT_SORT_INTLOC);
  return new_ast(
    z3::loc2int(to_solver_smt_ast<z3_smt_ast>(l)->a),
    this->mk_int_sort()
  );
}

BigInt z3_slhv_convt::get_bv(smt_astt a, bool is_signed)
{
  log_error("SLHV does not support bv");
  abort();
}

smt_astt z3_slhv_convt::mk_smt_symbol(const std::string &name, smt_sortt s)
{
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

smt_sortt z3_slhv_convt::convert_slhv_sorts(const type2tc &type)
{
  switch (type->type_id) {
    case type2t::intheap_id: return mk_intheap_sort();
    case type2t::intloc_id: return mk_intloc_sort();
    default: {
      log_error("Unexpected type for SLHV");
      abort();
    }
  }
}

smt_astt z3_slhv_convt::convert_ast(const expr2tc &expr)
{
  // log_debug("SLHV", "------------------------------- convert ast -----------------------------");
  // expr->dump();

  smt_cachet::const_iterator cache_result = smt_cache.find(expr);
  if (cache_result != smt_cache.end())
    return (cache_result->ast);

  std::vector<smt_astt> args;
  args.reserve(expr->get_num_sub_exprs());

  switch (expr->expr_id)
  {
    case expr2t::pointer_object_id:
    case expr2t::same_object_id:
    case expr2t::constant_intloc_id:
    case expr2t::constant_intheap_id:
    case expr2t::location_of_id:
    case expr2t::field_of_id:
    case expr2t::heap_region_id:
      break; // Don't convert their operands
    default:
    {
      // Convert all the arguments and store them in 'args'.
      unsigned int i = 0;
      expr->foreach_operand(
        [this, &args, &i](const expr2tc &e) { args[i++] = convert_ast(e); });
    }
  }

  smt_astt a;
  switch (expr->expr_id)
  {
    case expr2t::constant_intloc_id:
    case expr2t::constant_intheap_id:
    case expr2t::constant_heap_region_id:
    case expr2t::disjh_id:
    case expr2t::heap_region_id:
    case expr2t::location_of_id:
    case expr2t::field_of_id:
    case expr2t::points_to_id:
    case expr2t::uplus_id:
    case expr2t::locadd_id:
    case expr2t::heap_update_id:
    case expr2t::heap_contain_id:
    case expr2t::heap_append_id:
    case expr2t::heap_delete_id:
    {
      a = convert_slhv_opts(expr, args); 
      break;
    }

    case expr2t::constant_int_id:
    case expr2t::constant_bool_id:
    case expr2t::symbol_id:
    {
      a = convert_terminal(expr);
      break;
    }
    case expr2t::add_id:
    {
      const add2t &add = to_add2t(expr);
      a = mk_add(args[0], args[1]);
      break;
    }
    case expr2t::sub_id:
    {
      const sub2t &sub = to_sub2t(expr);
      a = mk_sub(args[0], args[1]);
      break;
    }
    case expr2t::same_object_id:
    {
      const same_object2t& so = to_same_object2t(expr);
      args[0] = this->project(so.side_1);
      args[1] = this->project(so.side_2);
      a = mk_eq(args[0], args[1]);
      break;
    }
    case expr2t::pointer_object_id:
    {
      const pointer_object2t &obj = to_pointer_object2t(expr);
      const expr2tc *ptr = &obj.ptr_obj;

      args[0] = convert_ast(*ptr);
      a = args[0];
      break;
    }
    case expr2t::typecast_id:
    {
      a = convert_slhv_typecast(expr);
      break;
    }
    case expr2t::if_id:
    {
      // Only attempt to handle struct.s
      const if2t &if_ref = to_if2t(expr);
      args[0] = convert_ast(if_ref.cond);
      args[1] = convert_ast(if_ref.true_value);
      args[2] = convert_ast(if_ref.false_value);
      a = args[1]->ite(this, args[0], args[2]);
      break;
    }
    case expr2t::equality_id:
    {
      auto eq = to_equality2t(expr);
      a = args[0]->eq(this, args[1]);
      break;
    }
    case expr2t::notequal_id:
    {
      auto neq = to_notequal2t(expr);
      a = args[0]->eq(this, args[1]);
      a = mk_not(a);
      break;
    }
    case expr2t::lessthan_id:
    {
      const lessthan2t &lt = to_lessthan2t(expr);
      a = mk_lt(args[0], args[1]);
      break;
    }
    case expr2t::lessthanequal_id:
    {
      const lessthanequal2t &lte = to_lessthanequal2t(expr);
      a = mk_le(args[0], args[1]);
      break;
    }
    case expr2t::greaterthan_id:
    {
      const greaterthan2t &gt = to_greaterthan2t(expr);
      a = mk_gt(args[0], args[1]);
      break;
    }
    case expr2t::greaterthanequal_id:
    {
      const greaterthanequal2t &gte = to_greaterthanequal2t(expr);
      // Pointer relation:
      a = mk_ge(args[0], args[1]);
      break;
    }
    case expr2t::implies_id:
    {
      a = mk_implies(args[0], args[1]);
      break;
    }
    case expr2t::not_id:
    {
      assert(is_bool_type(expr));
      a = mk_not(args[0]);
      break;
    }
    case expr2t::neg_id:
    {
      const neg2t &neg = to_neg2t(expr);
      a = mk_neg(args[0]);
      break;
    }
    case expr2t::and_id:
    {
      a = mk_and(args[0], args[1]);
      break;
    }
    case expr2t::or_id:
    {
      a = mk_or(args[0], args[1]);
      break;
    }
    default:
    {
      log_error("Couldn't convert expression in unrecognised format\n{}", *expr);
      abort();
    }
  }

  struct smt_cache_entryt entry = {expr, a, ctx_level};
  smt_cache.insert(entry);

  // log_debug("SLHV", "====================== converted reuslt: ");
  // a->dump();
  // log_debug("SLHV", "-------------------------------------------------------------------------");
  return a;
}

smt_astt
z3_slhv_convt::convert_slhv_opts(
  const expr2tc &expr, const std::vector<smt_astt>& args)
{
  switch (expr->expr_id)
  {
    case expr2t::constant_intloc_id:
      return mk_nil();
    case expr2t::constant_intheap_id:
      return mk_emp();
    case expr2t::constant_heap_region_id:
    {
      const constant_heap_region2t &const_reg = to_constant_heap_region2t(expr);
      const intheap_type2t &_type = to_intheap_type(expr->type);
      smt_astt base_loc = convert_ast(_type.location);

      std::vector<smt_astt> pt_vec;
      for (unsigned int i = 0; i < const_reg.datatype_members.size(); i++)
      {
        smt_astt loc =
          i == 0 ? base_loc : mk_locadd(base_loc, mk_smt_int(BigInt(i)));
        pt_vec.push_back(mk_pt(loc, args[i]));
      }
      return pt_vec.size() == 1 ? pt_vec[0] : mk_uplus(pt_vec);
    }
    case expr2t::disjh_id:
    {
      const disjh2t &disj = to_disjh2t(expr);
      int n = 0;
      smt_astt res;
      for (unsigned int i = 0; i < disj.other_heaps.size(); i++)
      {
        if (disj.is_sliced[i]) continue;
        smt_astt disj = mk_disjh(args[0], args[i + 1]);
        res = n == 0 ? disj : mk_and(res, disj);
        ++n;
      }
      return n == 0 ? mk_smt_bool(true) : res;
    }
    case expr2t::heap_region_id:
    {
      const intheap_type2t &_type = to_intheap_type(expr->type);

      smt_astt base_loc = convert_ast(_type.location);
      
      std::vector<smt_astt> pt_vec;
      if (_type.is_aligned)
      {
        for (unsigned int i = 0; i < _type.field_types.size(); i++)
        {
          smt_astt loc = i == 0 ? base_loc : mk_locadd(base_loc, mk_smt_int(BigInt(i)));
          smt_sortt sort =
            is_pointer_type(_type.field_types[i]) ?
              mk_intloc_sort() : mk_int_sort();
          std::string name =
            mk_fresh_name(
              is_pointer_type(_type.field_types[i]) ?
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
            base_loc,
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

      smt_astt loc;
      if (is_intheap_type(locof.source_heap))
      {
        const expr2tc &heap_region = locof.source_heap;
        const intheap_type2t &_type = to_intheap_type(heap_region->type);
        loc = convert_ast(_type.location);
      }
      else if (is_symbol2t(locof.source_heap) && 
          (is_intloc_type(locof.source_heap) ||
          is_scalar_type(locof.source_heap)))
      {
        std::string loc_name =
          to_symbol2t(locof.source_heap).get_symbol_name() + std::string("_LOC_");
        loc = mk_smt_symbol(loc_name, mk_intloc_sort());
      }
      else if (is_field_of2t(locof.source_heap))
      {
        const field_of2t &fieldof = to_field_of2t(locof.source_heap);
        if(!is_intheap_type(fieldof.source_heap->type) ||
           !to_intheap_type(fieldof.source_heap->type).is_region ||
           is_nil_expr(to_intheap_type(fieldof.source_heap->type).location))
        {
          log_error("Incomplete intheap type for field of");
          fieldof.dump();
          abort();
        }

        const intheap_type2t &_type = to_intheap_type(fieldof.source_heap->type);
        loc = mk_locadd(
          convert_ast(_type.location),
          convert_ast(fieldof.operand)
        );
      }
      else
      {
        log_error("Do not support yet");
        locof.source_heap->dump();
        abort();
      }
      return loc;
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
    {
      const field_of2t &field_of = to_field_of2t(expr);

      if (is_constant_intheap2t(field_of.source_heap))
        return
          mk_fresh(
            convert_sort(field_of.type),
            mk_fresh_name("invalid_fieldof_")
          );

      if (!is_constant_int2t(field_of.operand))
      {
        log_error("Wrong field");
        abort();
      }

      const expr2tc &heap_region = field_of.source_heap;
      const intheap_type2t &_type = to_intheap_type(heap_region->type);
      const expr2tc &field = field_of.operand;
      unsigned int _field = to_constant_int2t(field).value.to_uint64();

      smt_astt h = convert_ast(heap_region);
      smt_astt source_loc = convert_ast(_type.location);
      smt_astt l = _field == 0 ?
        source_loc : mk_locadd(source_loc, convert_ast(field));

      smt_sortt s1;
      if (is_pointer_type(_type.field_types[_field]))
        s1 = mk_intloc_sort();
      else
        s1 = mk_int_sort();
      smt_astt v1 = mk_fresh(s1, mk_fresh_name(std::string("_loaded_val_")));

      smt_astt pt = mk_pt(l, v1);
      smt_astt load_success = mk_subh(pt, h);
      smt_astt load_fail = mk_eq(h, mk_emp());
      smt_astt load_res = mk_or(load_success, load_fail);
      assert_ast(load_res);

      return v1;
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

      smt_astt h = args[0];
      smt_astt field = args[1];
      smt_astt source_loc = convert_ast(_type.location);
      smt_astt l = _field == 0 ? source_loc : mk_locadd(source_loc, field);
      smt_astt v = convert_ast(upd_value);

      smt_astt h1 = mk_fresh(h->sort, mk_fresh_name(std::string("_tmp_heap_")));
      smt_astt v1 = mk_fresh(v->sort, mk_fresh_name(std::string("_tmp_val_")));

      smt_astt heap_state = mk_eq(h, mk_uplus(h1, mk_pt(l, v1)));
      assert_ast(heap_state);

      return mk_uplus(h1, mk_pt(l, v));
    }
    case expr2t::heap_delete_id:
    {
      const heap_delete2t &heap_del = to_heap_delete2t(expr);

      smt_astt h = args[0];
      smt_astt l = args[1];

      smt_astt h1 = mk_fresh(h->sort, mk_fresh_name(std::string("_tmp_heap_")));
      smt_astt v1 = mk_fresh(mk_int_sort(), mk_fresh_name(std::string("_tmp_val_")));

      smt_astt nl =
        mk_fresh(
          mk_intloc_sort(),
          mk_fresh_name(std::string("_assigned_loc_"))
        );
      smt_astt heap_state = 
        mk_and(mk_eq(nl, l), mk_eq(h, mk_uplus(h1, mk_pt(nl, v1))));

      assert_ast(heap_state);

      return h1;
    }
    case expr2t::same_object_id:
    {
      // Do project for SLHV
      const same_object2t& same = to_same_object2t(expr);
      smt_astt p1 = this->project(same.side_1);
      smt_astt p2 = this->project(same.side_2);
      smt_astt eq = mk_eq(p1, p2);
      return eq;
    }
    default:
    {
      log_error("Invalid SLHV operations!!!");
      abort();
    }
  }
}

smt_astt z3_slhv_convt::convert_slhv_typecast(const expr2tc &expr)
{
  if (!is_typecast2t(expr))
  {
    log_error("Wrong typecast expr");
    expr->dump();
    abort();
  }

  const typecast2t &cast = to_typecast2t(expr);

  smt_astt a;
  if ((is_pointer_type(cast.from->type) && is_intloc_type(cast.type)) ||
      (is_pointer_type(cast.type) && is_intloc_type(cast.from->type)))
    a = convert_ast(cast.from);
  else if (
      (is_pointer_type(cast.from->type) || is_intloc_type(cast.from->type)) &&
      (is_signedbv_type(cast.type) || is_unsignedbv_type(cast.type)))
    return a = mk_loc2int(convert_ast(cast.from));
  else
    a = convert_typecast(expr);
  
  return a;
}

smt_astt z3_slhv_convt::project(const expr2tc &expr)
{
  if (is_constant_intloc2t(expr))
    return mk_nil();
  else if (is_symbol2t(expr))
  {
    if (is_intheap_type(expr))
    {
      const intheap_type2t &_type = to_intheap_type(expr->type);
      return this->project(_type.location);
    }

    if (is_intloc_type(expr) || is_pointer_type(expr))
      return convert_ast(expr);

    log_error("Wrong symbol for projection");
    expr->dump();
    abort();
  }
  else if (is_location_of2t(expr))
    return convert_ast(expr);
  else if (is_field_of2t(expr))
    return convert_ast(expr);
  else if (is_typecast2t(expr))
    return this->project(to_typecast2t(expr).from);
  else if (is_locadd2t(expr))
    return this->project(to_locadd2t(expr).location);
  else if (is_if2t(expr))
  {
    const if2t &_if = to_if2t(expr);
    smt_astt cond = convert_ast(_if.cond);
    smt_astt t = this->project(_if.true_value);
    smt_astt f = this->project(_if.false_value);
    return mk_ite(cond, t, f);
  }
  else
  {
    log_error("Do not support project");
    expr->dump();
    abort();
  }
}

void z3_slhv_convt::dump_smt()
{
  const std::string &path = options.get_option("output");
  if(path == "-") {
    print_smt_formulae(std::cout);
  } else {
    std::ofstream out(path);
    print_smt_formulae(out);
  }
}

void z3_slhv_convt::print_smt_formulae(std::ostream& dest)
{
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