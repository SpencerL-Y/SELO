#ifndef _ESBMC_SOLVERS_Z3_SLHV_CONV_H
#define _ESBMC_SOLVERS_Z3_SLHV_CONV_H

// this file does not follow the translation procedure in the 

#include <solvers/smt/smt_conv.h>
#include <z3++.h>


class z3_slhv_smt_ast : public solver_smt_ast<z3::expr>
{
public:
  using solver_smt_ast<z3::expr>::solver_smt_ast;
  ~z3_slhv_smt_ast() override = default;

  smt_astt update(smt_convt *ctx,
    smt_astt value,
    unsigned int idx,
    expr2tc idx_expr)
    const override;

  smt_astt project(smt_convt *ctx, unsigned int elem) const override;

  void dump() const override;
};

/* Be sure to not make smt_convt a *virtual* base class: our dtor ~z3_convt()
 * erases all smt_asts early. */

class z3_slhv_convt : public smt_convt {
public:
    z3_slhv_convt(const namespacet &ns, const optionst &options);
    ~z3_slhv_convt() override;
public:
    // interface for translation
    // TODO slhv: move to the api later, currently we use the smt-lib2 string translation
    // interfaces of smt_convt need implementation
    void push_ctx() override;
    void pop_ctx() override;

    void assert_ast(smt_astt a) override;
    resultt dec_solve() override;
    const std::string solver_text() override;

    // terminal making 
    smt_astt mk_smt_int(const BigInt &theint) override;
    smt_astt mk_smt_real(const std::string &str) override;
    smt_astt mk_smt_bv(const BigInt &theint, smt_sortt s) override;
    smt_astt mk_smt_bool(bool val) override;
    smt_astt mk_smt_symbol(const std::string &name, smt_sortt s) override;
    smt_astt mk_extract(smt_astt a, unsigned int high, unsigned int low) override;
    smt_astt mk_sign_ext(smt_astt a, unsigned int topwidth) override;
    smt_astt mk_zero_ext(smt_astt a, unsigned int topwidth) override;
    smt_astt mk_concat(smt_astt a, smt_astt b) override;
    // logical connection making 
    smt_astt mk_ite(smt_astt cond, smt_astt t, smt_astt f) override;
    smt_astt mk_or(smt_astt a, smt_astt b) override;
    smt_astt mk_and(smt_astt a, smt_astt b) override;
    smt_astt mk_implies(smt_astt a, smt_astt b) override;
    smt_astt mk_not(smt_astt a) override;

    // numeral assertions
    smt_astt mk_lt(smt_astt a, smt_astt b) override;
    smt_astt mk_le(smt_astt a, smt_astt b) override;
    smt_astt mk_gt(smt_astt a, smt_astt b) override;
    smt_astt mk_ge(smt_astt a, smt_astt b) override;
    smt_astt mk_eq(smt_astt a, smt_astt b) override;
    smt_astt mk_neq(smt_astt a, smt_astt b) override;
    // numeral terms
    smt_astt mk_add(smt_astt a, smt_astt b) override;

    // heap terms
    smt_astt mk_pt(smt_astt a, smt_astt b);
    smt_astt mk_uplus(smt_astt a, smt_astt b);
    smt_astt mk_emp();
    // loc terms
    smt_astt mk_locadd(smt_astt loc, smt_astt i);
    smt_astt mk_nil();


    // value obtaining from solver, not supported here
    bool get_bool(smt_astt a) override;
    BigInt get_bv(smt_astt a, bool is_signed) override;
    void dump_smt() override;

    // sort making 
    smt_sortt mk_bool_sort() override;
    smt_sortt mk_int_sort() override;
    smt_sortt mk_intloc_sort();
    smt_sortt mk_intheap_sort();


    // ast converting
    smt_astt convert_ast_slhv(const expr2tc &expr);
    smt_sortt convert_sort_slhv(const type2tc &type);
    smt_astt convert_assign_slhv(const expr2tc &expr);



    std::vector<smt_astt> assertions;    
    z3::context z3_ctx;
};

#endif