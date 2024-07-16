
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include <iostream>
#include <sstream>
#include<vector>
#include "z3++.h"

using namespace z3;


void slhv_cases() {
    context c;
    expr hvar1 = c.hvar_const("hvar1");
    expr hvar2 = c.hvar_const("hvar2");
    expr uplushvars = uplus(hvar1, hvar2);
    expr emp = c.emp_const();
    expr nil = c.nil_const();
    expr data1 = c.int_const("datavar");
    expr locvar = c.locvar_const("addrvar");
    std::cout << data1.get_sort() << std::endl;
    expr datar = data_record(data1);
    expr pt_test = points_to(locvar, data1);
    std::cout << hvar1 << std::endl;
    std::cout << data1 << std::endl; 
    std::cout << uplushvars << std::endl;
    std::cout << pt_test << std::endl;
    solver s(c,"SLHV");
    expr constr1 = (hvar1 == hvar2);
    s.add(constr1);
    s.check();
}


int main() {

    try {
    slhv_cases(); std::cout << "\n";
        std::cout << "done\n";
    }
    catch (exception & ex) {
        std::cout << "unexpected error: " << ex << "\n";
    }
    Z3_finalize_memory();
    return 0;

}
