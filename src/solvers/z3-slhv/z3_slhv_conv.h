#ifndef _ESBMC_SOLVERS_Z3_SLHV_CONV_H
#define _ESBMC_SOLVERS_Z3_SLHV_CONV_H

#include <map>

#include <solvers/z3/z3_conv.h>
#include <z3++.h>

class z3_slhv_convt : public z3_convt {
public:
    z3_slhv_convt(const namespacet &ns, const optionst &options);
    ~z3_slhv_convt() override;
public:
    // interface for translation
    // TODO slhv: move to the api later, currently we use the smt-lib2 string translation
    // interfaces of smt_convt need implementation

    // void assert_ast(smt_astt a) override;
    smt_convt::resultt dec_solve() override;
    const std::string solver_text() override;

    // sort making 
    smt_sortt mk_intheap_sort();
    smt_sortt mk_intloc_sort();
    smt_sortt mk_struct_sort(const type2tc &type) override;

    // constant and operators
    smt_astt mk_emp();
    smt_astt mk_nil();
    smt_astt mk_pt(smt_astt l, smt_astt v);
    smt_astt mk_uplus(smt_astt ht1, smt_astt ht2);
    smt_astt mk_uplus(std::vector<smt_astt> hts);
    smt_astt mk_subh(smt_astt ht1, smt_astt ht2);
    smt_astt mk_disjh(smt_astt ht1, smt_astt );
    smt_astt mk_locadd(smt_astt l, smt_astt o);
    smt_astt mk_heap_read(smt_astt h, smt_astt l, smt_sortt s);
    smt_astt mk_heap_write(smt_astt h, smt_astt l, smt_astt c);
    smt_astt mk_heap_delete(smt_astt h, smt_astt l);

    // value obtaining from solver, not supported here
    BigInt get_bv(smt_astt a, bool is_signed) override;

    // SLHV variable
    smt_astt mk_smt_symbol(const std::string &name, smt_sortt s) override;

    smt_sortt convert_slhv_sorts(const type2tc &type) override;

    smt_astt convert_ast(const expr2tc &expr) override;

    smt_astt
    convert_slhv_opts(const expr2tc &expr, const std::vector<smt_astt>& args) override;

    smt_astt project(const expr2tc &expr);

    void dump_smt() override;

private:
    void print_smt_formulae(std::ostream& dest);

    std::vector<smt_astt> assertions;
};

#endif