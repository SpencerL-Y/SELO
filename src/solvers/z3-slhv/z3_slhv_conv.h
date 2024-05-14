#ifndef _ESBMC_SOLVERS_Z3_SLHV_CONV_H
#define _ESBMC_SOLVERS_Z3_SLHV_CONV_H

// this file does not follow the translation procedure in the 

#include <solvers/smt/smt_conv.h>
#include <z3++.h>


class z3_slhv_smt_ast : public solver_smt_ast<z3::expr>
{
public:
  using solver_smt_ast<z3::expr>::solver_smt_ast;
  ~z3_smt_ast() override = default;

  smt_astt
  update(smt_convt *ctx, smt_astt value, unsigned int idx, expr2tc idx_expr)
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
    void push_ctx() override;
    void pop_ctx() override;

    void assert_ast(smt_astt a) override;
    resultt dec_solver() override;
    std::string solver_text() override;

    smt_astt mk_smt_int(const BigInt &theint) override;
    smt_astt mk_smt_real(const std::string &str) override;
    smt_astt mk_smt_bv(const BigInt &theint, smt_sortt s) override;
    smt_astt mk_smt_bool(bool val) override;
    smt_astt mk_smt_symbol(const std::string &name, smt_sortt s) override;
    smt_astt mk_extract(smt_astt a, unsigned int high, unsigned int low) override;
    smt_astt mk_sign_ext(smt_astt a, unsigned int topwidth) override;
    smt_astt mk_zero_ext(smt_astt a, unsigned int topwidth) override;
    smt_astt mk_concat(smt_astt a, smt_astt b) override;
    smt_astt mk_ite(smt_astt cond, smt_astt t, smt_astt f) override;
    bool get_bool(smt_astt a) override;
    BigInt get_bv(smt_astt a, bool is_signed) override;
    smt_astt overflow_arith(const expr2tc *&expr) override;
    
    void dump_smt() override;
    
}

#endif