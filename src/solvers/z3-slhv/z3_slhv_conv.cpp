#include <cassert>
#include <iostream>
#include <solvers/smt/smt_conv.h>
#include <z3_slhv_conv.h>


z3_slhv_convt::z3_slhv_convt(const namespacet &_ns, const optionst& _options) : smt_convt(_ns, _options) {
    // initialize the z3 based slhv converter here
}

z3_slhv_convt::~z3_slhv_convt() {
  delete_all_asts();
}
void z3_slhv_convt::push_ctx() {

}

void z3_slhv_convt::pop_ctx() {

}

void z3_slhv_convt::assert_ast(smt_astt a) {

}

smt_convt::resultt z3_slhv_convt::dec_solve() {
  return P_SMTLIB;
}

const std::string z3_slhv_convt::solver_text() {
  return "Z3-slhv";
}

smt_astt z3_slhv_convt::mk_smt_int(const BigInt &theint) {

}

smt_astt z3_slhv_convt::mk_smt_real(const std::string &str) {

}

smt_astt z3_slhv_convt::mk_smt_bv(const BigInt &theint, smt_sortt s) {

}
smt_astt z3_slhv_convt::mk_smt_bool(bool val){
  
}
smt_astt z3_slhv_convt::mk_smt_symbol(const std::string &name, smt_sortt s){
  
}
smt_astt z3_slhv_convt::mk_extract(smt_astt a, unsigned int high, unsigned int low){
  
}
smt_astt z3_slhv_convt::mk_sign_ext(smt_astt a, unsigned int topwidth){
  
}
smt_astt z3_slhv_convt::mk_zero_ext(smt_astt a, unsigned int topwidth){
  
}
smt_astt z3_slhv_convt::mk_concat(smt_astt a, smt_astt b){
  
}
smt_astt z3_slhv_convt::mk_ite(smt_astt cond, smt_astt t, smt_astt f){
  
}
bool z3_slhv_convt::get_bool(smt_astt a){
  
}
BigInt z3_slhv_convt::get_bv(smt_astt a, bool is_signed){
  
}
smt_astt z3_slhv_convt::overflow_arith(const expr2tc &expr){
  
}

void z3_slhv_convt::dump_smt(){
  
}