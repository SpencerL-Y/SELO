#include <cassert>
#include <goto-symex/dynamic_allocation.h>
#include <goto-symex/goto_symex.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <irep2/irep2.h>
#include <util/std_expr.h>

void goto_symext::default_replace_dynamic_allocation(expr2tc &expr)
{
  expr->Foreach_operand([this](expr2tc &e) {
    if (!is_nil_expr(e))
      default_replace_dynamic_allocation(e);
  });

  bool use_old_encoding = !options.get_bool_option("z3-slhv");
  if (is_valid_object2t(expr))
  {
    /* alloc */
    // replace with CPROVER_alloc[POINTER_OBJECT(...)]
    if(use_old_encoding) {
      const valid_object2t &obj = to_valid_object2t(expr);

      expr2tc obj_expr = pointer_object2tc(pointer_type2(), obj.value);

      expr2tc alloc_arr_2;
      migrate_expr(symbol_expr(*ns.lookup(valid_ptr_arr_name)), alloc_arr_2);

      expr2tc index_expr = index2tc(get_bool_type(), alloc_arr_2, obj_expr);
      expr = index_expr;
    } else {
      const valid_object2t &obj = to_valid_object2t(expr);
      const expr2tc &heap_region = obj.value;
      if (!is_intheap_type(heap_region->type) ||
          !to_intheap_type(heap_region->type).is_region)
      {
        log_error("Wrong object");
        abort();
      }
      const intheap_type2t &type = to_intheap_type(heap_region->type);

      if (type.is_alloced)
      {
        expr2tc loc = type.location;
        cur_state->get_original_name(loc);

        bool is_in_frame = false;
        goto_symex_statet::framet &frame = cur_state->top();
        for (auto const &it : frame.local_heap_regions)
        {
          expr2tc alloced_loc = to_intheap_type(it->type).location;
          cur_state->get_original_name(alloced_loc);

          if (to_symbol2t(loc).get_symbol_name() != 
              to_symbol2t(alloced_loc).get_symbol_name())
            continue;
          
          is_in_frame = true;
        }

        if (is_in_frame)
          expr = not2tc(equality2tc(heap_region, gen_emp()));
        else
        {
          // use alloc_size_heap
          expr2tc alloc_size_heap;
          migrate_expr(symbol_expr(*ns.lookup(alloc_size_heap_name)), alloc_size_heap);

          unsigned int &nondet_counter = get_nondet_counter();
          nondet_counter++;
          expr2tc size_sym =
            symbol2tc(
              get_int64_type(),
              std::string("SOME_SIZE_") + std::to_string(nondet_counter)
            );

          expr2tc pt = points_to2tc(loc, size_sym);
          expr2tc disj = disjh2tc(alloc_size_heap);
          to_disjh2t(disj).do_disjh(pt);
          expr = not2tc(disj);
        }
      }
      else
        expr = not2tc(equality2tc(heap_region, gen_emp()));
    }
  }
  else if (is_invalid_pointer2t(expr))
  {
    /* (!valid /\ dynamic) \/ invalid */
    const invalid_pointer2t &ptr = to_invalid_pointer2t(expr);

    expr2tc obj_expr = pointer_object2tc(pointer_type2(), ptr.ptr_obj);

    if (use_old_encoding)
    {
      expr2tc alloc_arr_2;
      migrate_expr(symbol_expr(*ns.lookup(valid_ptr_arr_name)), alloc_arr_2);

      expr2tc index_expr = index2tc(get_bool_type(), alloc_arr_2, obj_expr);
      expr2tc notindex = not2tc(index_expr);

      // XXXjmorse - currently we don't correctly track the fact that stack
      // objects change validity as the program progresses, and the solver is
      // free to guess that a stack ptr is invalid, as we never update
      // __ESBMC_alloc for stack ptrs.
      // So, add the precondition that invalid_ptr only ever applies to dynamic
      // objects.

      expr2tc sym_2;
      migrate_expr(symbol_expr(*ns.lookup(dyn_info_arr_name)), sym_2);

      expr2tc ptr_obj = pointer_object2tc(pointer_type2(), ptr.ptr_obj);
      expr2tc is_dyn = index2tc(get_bool_type(), sym_2, ptr_obj);

      // Catch free pointers: don't allow anything to be pointer object 1, the
      // invalid pointer.
      type2tc ptr_type = pointer_type2tc(get_empty_type());
      expr2tc invalid_object = symbol2tc(ptr_type, "INVALID");
      expr2tc isinvalid = equality2tc(ptr.ptr_obj, invalid_object);

      expr2tc is_not_bad_ptr = and2tc(notindex, is_dyn);
      expr2tc is_valid_ptr = or2tc(is_not_bad_ptr, isinvalid);

      expr = is_valid_ptr;
    }
    else
    {
      log_status("replace invalid pointer");      
      obj_expr->dump();

      expr2tc alloc_size_heap;
      migrate_expr(symbol_expr(*ns.lookup(alloc_size_heap_name)), alloc_size_heap);

      unsigned int &nondet_counter = get_nondet_counter();
      nondet_counter++;
      expr2tc size_sym =
        symbol2tc(
          get_int64_type(),
          std::string("SOME_SIZE_") + std::to_string(nondet_counter)
        );

      expr2tc loc;
      expr2tc extra_eq;
      if (!is_if2t(obj_expr))
        loc = obj_expr;
      else
      {
        loc =
          symbol2tc(
            get_int64_type(),
            std::string("assigned_loc_") + std::to_string(nondet_counter)
          );
        extra_eq = equality2tc(loc, obj_expr);
      }

      expr2tc pt = points_to2tc(loc, size_sym);
      expr2tc is_invalid = disjh2tc(alloc_size_heap);
      to_disjh2t(is_invalid).do_disjh(pt);
      if (!is_nil_expr(extra_eq))
        is_invalid = and2tc(extra_eq, is_invalid);

      expr = is_invalid;
    }
  }
  else if (is_deallocated_obj2t(expr))
  {
    /* !alloc */
    // replace with CPROVER_alloc[POINTER_OBJECT(...)]
    const deallocated_obj2t &obj = to_deallocated_obj2t(expr);

    expr2tc obj_expr = pointer_object2tc(pointer_type2(), obj.value);

    expr2tc alloc_arr_2;
    migrate_expr(symbol_expr(*ns.lookup(valid_ptr_arr_name)), alloc_arr_2);

    if (is_symbol2t(obj.value))
      expr = index2tc(get_bool_type(), alloc_arr_2, obj_expr);
    else
    {
      expr2tc index_expr = index2tc(get_bool_type(), alloc_arr_2, obj_expr);
      expr = not2tc(index_expr);
    }
  }
  else if (is_dynamic_size2t(expr))
  {
    // replace with CPROVER_alloc_size[POINTER_OBJECT(...)]
    //nec: ex37.c
    const dynamic_size2t &size = to_dynamic_size2t(expr);

    expr2tc obj_expr = pointer_object2tc(pointer_type2(), size.value);

    expr2tc alloc_arr_2;
    migrate_expr(symbol_expr(*ns.lookup(alloc_size_arr_name)), alloc_arr_2);

    expr2tc index_expr = index2tc(size_type2(), alloc_arr_2, obj_expr);
    expr = index_expr;
  }
}
