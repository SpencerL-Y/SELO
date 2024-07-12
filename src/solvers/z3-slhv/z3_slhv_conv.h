#ifndef _ESBMC_SOLVERS_Z3_SLHV_CONV_H
#define _ESBMC_SOLVERS_Z3_SLHV_CONV_H

// this file does not follow the translation procedure in the 

// #include <solvers/smt/smt_conv.h>
#include <solvers/z3/z3_conv.h>
#include <z3++.h>

// class z3_slhv_smt_ast : public solver_smt_ast<z3::expr>
// {
// public:
//   using solver_smt_ast<z3::expr>::solver_smt_ast;
//   ~z3_slhv_smt_ast() override = default;

//   smt_astt update(smt_convt *ctx,
//     smt_astt value,
//     unsigned int idx,
//     expr2tc idx_expr)
//     const override;

//   smt_astt project(smt_convt *ctx, unsigned int elem) const override;

//   void dump() const override;
// };

class z3_slhv_convt : public z3_convt {
public:
    z3_slhv_convt(const namespacet &ns, const optionst &options);
    ~z3_slhv_convt() override;
public:
    // interface for translation
    // TODO slhv: move to the api later, currently we use the smt-lib2 string translation
    // interfaces of smt_convt need implementation

    // void assert_ast(smt_astt a) override;
    resultt dec_solve() override;
    const std::string solver_text() override;

    // constant and operators
    smt_astt mk_emp();
    smt_astt mk_nil();
    smt_astt mk_pt(smt_astt a, smt_astt b);
    smt_astt mk_uplus(smt_astt a, smt_astt b);
    smt_astt mk_subh(smt_astt a, smt_astt b);
    smt_astt mk_disjh(smt_astt a, smt_astt b);
    smt_astt mk_locadd(smt_astt a, smt_astt b);

    // value obtaining from solver, not supported here
    bool get_bool(smt_astt a) override;
    BigInt get_bv(smt_astt a, bool is_signed) override;

    // sort making 
    smt_sortt mk_intheap_sort();
    smt_sortt mk_intloc_sort();
    smt_sortt mk_struct_sort(const type2tc &type) override;

    smt_sortt convert_slhv_sorts(const type2tc &type) override;
    smt_astt
    convert_slhv_opts(const expr2tc &expr, const std::vector<smt_astt>& args) override;

private:
    std::vector<smt_astt> assertions;
};

#endif