#include <iostream>
#include "z3++.h"

// ------------------------------------------------------------
//  Bitmask utilities
// ------------------------------------------------------------




int main() {
    z3::context ctx;
    z3::solver s(ctx);
    z3::expr x = ctx.int_const("x");
    s.add(x > 5);
    if (s.check() == z3::sat) {
        std::cout << "sat!\n";
    } else {
        std::cout << "unsat\n";
    }
}
