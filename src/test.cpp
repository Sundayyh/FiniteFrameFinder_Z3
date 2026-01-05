#include <iostream>
#include "z3++.h"

// ------------------------------------------------------------
//  Bitmask utilities
// ------------------------------------------------------------



// ------------------------------------------------------------
//  Axiom encoders
// ------------------------------------------------------------



int main() {
    z3::context ctx;           // Create context (manages all Z3 objects)
    z3::solver s(ctx);         // Create solver instance
    z3::expr x = ctx.int_const("x");  // Declare variable
    s.add(x > 5);              // Add constraint
    z3::check_result result = s.check();  // Check satisfiability
    if (result == z3::sat) {
        z3::model m = s.get_model();  // Get solution
        std::cout << "Sat! The model is:\n" << m  << "\n";
    }
}
