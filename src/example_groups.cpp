#include <iostream>
#include <vector>
#include "z3++.h"

// ============================================================
//  Group Model Finder: Demonstrates Z3 SMT Workflow
// ============================================================
//  Goal: Find a group structure (G, *, e) on domain {0..n-1}
//  
//  Workflow:
//  1. Create FREE VARIABLES: multiplication table mul[i][j]
//  2. Add THEORY CONSTRAINTS: group axioms
//  3. SOLVE: let Z3 find a satisfying model
//  4. EXTRACT: read the multiplication table from model
// ============================================================

class GroupFinder {
    z3::context& ctx;
    int n;  // cardinality
    std::vector<std::vector<z3::expr>> mul_table;  // mul_table[i][j] = i*j
    z3::expr identity;  // identity element
    
public:
    GroupFinder(z3::context& c, int cardinality) 
        : ctx(c), n(cardinality), identity(ctx.int_const("e")) {
        
        // Step 1: CREATE FREE VARIABLES
        // Each entry mul_table[i][j] represents i*j in the group
        for (int i = 0; i < n; ++i) {
            mul_table.emplace_back();
            for (int j = 0; j < n; ++j) {
                std::string var_name = "m_" + std::to_string(i) + "_" + std::to_string(j);
                mul_table[i].push_back(ctx.int_const(var_name.c_str()));
            }
        }
    }
    
    // Step 2: ENCODE THEORY CONSTRAINTS (Group Axioms)
    void add_group_axioms(z3::solver& s) {
        std::cout << "Encoding group axioms for cardinality " << n << "...\n";
        
        // Domain constraint: all values in {0, ..., n-1}
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) {
                s.add(mul_table[i][j] >= 0 && mul_table[i][j] < n);
            }
        }
        s.add(identity >= 0 && identity < n);
        
        // AXIOM 1: Identity element exists
        // ∀a. e*a = a ∧ a*e = a
        for (int a = 0; a < n; ++a) {
            // When identity is i, then mul_table[i][a] = a and mul_table[a][i] = a
            z3::expr_vector left_id(ctx), right_id(ctx);
            for (int e = 0; e < n; ++e) {
                left_id.push_back(z3::implies(identity == e, mul_table[e][a] == a));
                right_id.push_back(z3::implies(identity == e, mul_table[a][e] == a));
            }
            s.add(z3::mk_and(left_id));  // ALL implications must hold (only one has true antecedent)
            s.add(z3::mk_and(right_id)); // ALL implications must hold (only one has true antecedent)
        }
        
        // AXIOM 2: Associativity
        // ∀a,b,c. (a*b)*c = a*(b*c)
        for (int a = 0; a < n; ++a) {
            for (int b = 0; b < n; ++b) {
                for (int c = 0; c < n; ++c) {
                    // (a*b)*c: mul_table[mul_table[a][b]][c]
                    // a*(b*c): mul_table[a][mul_table[b][c]]
                    z3::expr_vector lhs_options(ctx), rhs_options(ctx);
                    
                    for (int ab = 0; ab < n; ++ab) {
                        for (int bc = 0; bc < n; ++bc) {
                            z3::expr condition = mul_table[a][b] == ab && mul_table[b][c] == bc;
                            z3::expr equality = mul_table[ab][c] == mul_table[a][bc];
                            s.add(z3::implies(condition, equality));
                        }
                    }
                }
            }
        }
        
        // AXIOM 3: Inverse exists
        // ∀a. ∃b. a*b = e ∧ b*a = e
        for (int a = 0; a < n; ++a) {
            z3::expr_vector has_right_inv(ctx), has_left_inv(ctx);
            for (int b = 0; b < n; ++b) {
                has_right_inv.push_back(mul_table[a][b] == identity);
                has_left_inv.push_back(mul_table[b][a] == identity);
            }
            s.add(z3::mk_or(has_right_inv));  // ∃b. a*b = e
            s.add(z3::mk_or(has_left_inv));   // ∃b. b*a = e
        }
        
        std::cout << "Axioms encoded.\n";
    }
    
    // Step 4: EXTRACT MODEL - display the multiplication table
    void display_model(z3::model& m) {
        int e = m.eval(identity).get_numeral_int();
        std::cout << "\n=== GROUP MODEL FOUND ===\n";
        std::cout << "Identity element: " << e << "\n\n";
        std::cout << "Multiplication table (* operation):\n";
        std::cout << "  * |";
        for (int j = 0; j < n; ++j) std::cout << " " << j;
        std::cout << "\n----+";
        for (int j = 0; j < n; ++j) std::cout << "--";
        std::cout << "\n";
        
        for (int i = 0; i < n; ++i) {
            std::cout << "  " << i << " |";
            for (int j = 0; j < n; ++j) {
                int result = m.eval(mul_table[i][j]).get_numeral_int();
                std::cout << " " << result;
            }
            std::cout << "\n";
        }
        
        // Verify it's a valid group structure
        verify_group(m, e);
    }
    
    void verify_group(z3::model& m, int e) {
        std::cout << "\n=== VERIFICATION ===\n";
        
        // Extract concrete table
        std::vector<std::vector<int>> table(n, std::vector<int>(n));
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) {
                table[i][j] = m.eval(mul_table[i][j]).get_numeral_int();
            }
        }
        
        // Check identity
        bool identity_ok = true;
        for (int a = 0; a < n; ++a) {
            if (table[e][a] != a || table[a][e] != a) {
                identity_ok = false;
                break;
            }
        }
        std::cout << "✓ Identity: " << (identity_ok ? "PASS" : "FAIL") << "\n";
        
        // Check associativity
        bool assoc_ok = true;
        for (int a = 0; a < n && assoc_ok; ++a) {
            for (int b = 0; b < n && assoc_ok; ++b) {
                for (int c = 0; c < n && assoc_ok; ++c) {
                    int ab_c = table[table[a][b]][c];
                    int a_bc = table[a][table[b][c]];
                    if (ab_c != a_bc) {
                        assoc_ok = false;
                    }
                }
            }
        }
        std::cout << "✓ Associativity: " << (assoc_ok ? "PASS" : "FAIL") << "\n";
        
        // Check inverses
        bool inv_ok = true;
        for (int a = 0; a < n && inv_ok; ++a) {
            bool has_inv = false;
            for (int b = 0; b < n; ++b) {
                if (table[a][b] == e && table[b][a] == e) {
                    has_inv = true;
                    break;
                }
            }
            if (!has_inv) inv_ok = false;
        }
        std::cout << "✓ Inverses: " << (inv_ok ? "PASS" : "FAIL") << "\n";
    }
};

int main() {
    z3::context ctx;
    z3::solver s(ctx);
    
    // Find a group of cardinality 4
    int n = 7;
    GroupFinder finder(ctx, n);
    
    // Step 2: Add constraints
    finder.add_group_axioms(s);
    
    // Step 3: SOLVE - Let Z3 search for a model
    std::cout << "\nSearching for a group model...\n";
    z3::check_result result = s.check();
    
    if (result == z3::sat) {
        std::cout << "SAT - Model found!\n";
        z3::model m = s.get_model();
        finder.display_model(m);
    } else if (result == z3::unsat) {
        std::cout << "UNSAT - No group of this cardinality exists\n";
    } else {
        std::cout << "UNKNOWN - Solver couldn't determine\n";
    }
    
    return 0;
}
