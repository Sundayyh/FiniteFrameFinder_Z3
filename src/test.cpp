#include <iostream>
#include <vector>
#include <string>
#include <sstream>
#include <cassert>
#include "z3++.h"

// ============================================================
//  Bitmask Utilities
// ============================================================
//  Goal: represent set operations using bit operations whereby 
//  Omega = {0,..,n-1} and subset S ⊆ Omega is represented as 
//  an integer bitmask.
// ============================================================

namespace BitOps {
    // Check if element k is in the bitmask
    inline bool contains(int mask, int k) {
        return (mask & (1 << k)) != 0;
    }
    
    // Set union (bitwise OR)
    inline int set_union(int mask1, int mask2) {
        return mask1 | mask2;
    }
    
    // Set intersection (bitwise AND)
    inline int set_intersection(int mask1, int mask2) {
        return mask1 & mask2;
    }
    
    // Set complement with respect to universe of size n
    inline int set_complement(int mask, int n) {
        return ((1 << n) - 1) ^ mask;
    }
    
    // Check if mask1 ⊆ mask2
    inline bool is_subset(int mask1, int mask2) {
        return (mask1 & mask2) == mask1;
    }
    
    // Count elements in set (popcount)
    inline int cardinality(int mask) {
        int count = 0;
        while (mask) {
            count += mask & 1;
            mask >>= 1;
        }
        return count;
    }
    
    // Convert bitmask to string representation like "{0,2,3}"
    std::string to_string(int mask, int n) {
        std::ostringstream oss;
        oss << "{";
        bool first = true;
        for (int i = 0; i < n; ++i) {
            if (contains(mask, i)) {
                if (!first) oss << ",";
                oss << i;
                first = false;
            }
        }
        oss << "}";
        return oss.str();
    }
}

// ============================================================
//  FrameVariables - Holds Z3 symbolic variables
// ============================================================
//  Decoupled from solver; can be shared across multiple solvers
// ============================================================

class FrameVariables {
    z3::context& ctx;
    int n;              // Universe size
    int powerset_size;  // 2^n subsets
    std::vector<std::vector<z3::expr>> R;  // R[i][j] = (subset_i ≤ subset_j)

public:
    FrameVariables(z3::context& c, int universe_size)
        : ctx(c), n(universe_size), powerset_size(1 << universe_size) {
        
        // Create boolean matrix R[i][j]
        for (int i = 0; i < powerset_size; ++i) {
            R.emplace_back();
            for (int j = 0; j < powerset_size; ++j) {
                std::string var_name = "R_" + std::to_string(i) + "_" + std::to_string(j);
                R[i].push_back(ctx.bool_const(var_name.c_str()));
            }
        }
        std::cout << "Created " << (powerset_size * powerset_size) << " boolean variables\n";
    }

    // Accessors
    z3::context& context() { return ctx; }
    int universe_size() const { return n; }
    int size() const { return powerset_size; }
    z3::expr& get_R(int i, int j) { return R[i][j]; }
    const z3::expr& get_R(int i, int j) const { return R[i][j]; }
};

// ============================================================
//  AxiomEncoder - Methods to encode axioms into constraints
// ============================================================
//  Each axiom is a separate method; call directly as needed
// ============================================================

class AxiomEncoder {
    FrameVariables& vars;

public:
    AxiomEncoder(FrameVariables& v) : vars(v) {}

    // AXIOM: Transitivity - if i ≤ j and j ≤ k, then i ≤ k
    void encode_transitivity(z3::solver& s) {
        std::cout << "  Encoding transitivity...\n";
        int count = 0;
        for (int i = 0; i < vars.size(); ++i) {
            for (int j = 0; j < vars.size(); ++j) {
                for (int k = 0; k < vars.size(); ++k) {
                    // (R[i][j] ∧ R[j][k]) → R[i][k]
                    s.add(z3::implies(vars.get_R(i, j) && vars.get_R(j, k), vars.get_R(i, k)));
                    count++;
                }
            }
        }
        std::cout << "    Added " << count << " transitivity implications\n";
    }

    // AXIOM: Monotonicity - subset inclusion implies ordering
    void encode_monotonicity(z3::solver& s) {
        std::cout << "  Encoding monotonicity (subset inclusion → ordering)...\n";
        for (int i = 0; i < vars.size(); ++i) {
            for (int j = 0; j < vars.size(); ++j) {
                if (BitOps::is_subset(i, j)) {
                    s.add(vars.get_R(i, j));  // i ⊆ j → i ≤ j
                }
            }
        }
    }

    // AXIOM: Non-triviality - it is not the case that the full set Omega and the empty set stand in the relation R.
    void encode_non_triviality(z3::solver& s) {
        std::cout << "  Encoding non-triviality...\n";
        int full_set = vars.size() - 1;  // Assuming full set is the last subset
        int empty_set = 0;                // Assuming empty set is the first subset
        s.add(!vars.get_R(full_set, empty_set));
    }
};

// ============================================================
//  FrameFinder - Solver orchestrator
// ============================================================
//  Owns context, solver, variables, and encoder
// ============================================================

class FrameFinder {
    z3::context ctx;
    z3::solver s;
    FrameVariables vars;
    AxiomEncoder enc;

public:
    FrameFinder(int universe_size)
        : ctx(), s(ctx), vars(ctx, universe_size), enc(vars) {
        std::cout << "FrameFinder initialized for universe size " << universe_size << "\n";
        std::cout << "Powerset has " << vars.size() << " subsets\n";
    }

    // Accessors
    z3::solver& solver() { return s; }
    AxiomEncoder& encoder() { return enc; }
    FrameVariables& variables() { return vars; }

    // Solve and return result
    z3::check_result solve() {
        std::cout << "\nSearching for solution...\n";
        return s.check();
    }

    // Get model (call after SAT)
    z3::model get_model() {
        return s.get_model();
    }

    // Display model
    void display_model() {
        z3::model m = get_model();
        int ps = vars.size();
        int n = vars.universe_size();

        std::cout << "\n=== PARTIAL PREORDER FOUND ===\n\n";

        // Extract boolean matrix
        std::vector<std::vector<bool>> matrix(ps, std::vector<bool>(ps));
        for (int i = 0; i < ps; ++i) {
            for (int j = 0; j < ps; ++j) {
                matrix[i][j] = m.eval(vars.get_R(i, j)).is_true();
            }
        }

        // Display matrix
        std::cout << "Boolean Matrix R[i][j] (1 means subset_i ≤ subset_j):\n\n";
        std::cout << "     ";
        for (int j = 0; j < ps; ++j) {
            std::cout << " " << j;
            if (j < 10) std::cout << " ";
        }
        std::cout << "\n     ";
        for (int j = 0; j < ps; ++j) std::cout << "---";
        std::cout << "\n";

        for (int i = 0; i < ps; ++i) {
            std::cout << " " << i;
            if (i < 10) std::cout << " ";
            std::cout << " | ";
            for (int j = 0; j < ps; ++j) {
                std::cout << (matrix[i][j] ? "1" : "·") << "  ";
            }
            std::cout << " | " << BitOps::to_string(i, n) << "\n";
        }

        // Verify properties for tests
        verify_preorder(matrix);
        verify_monotonicity(matrix);
        verify_non_triviality(matrix);
    }

private:
    void verify_preorder(const std::vector<std::vector<bool>>& matrix) {
        int ps = vars.size();
        std::cout << "\n=== VERIFICATION ===\n";

        // Check reflexivity
        bool reflexive_ok = true;
        for (int i = 0; i < ps; ++i) {
            if (!matrix[i][i]) {
                reflexive_ok = false;
                break;
            }
        }
        std::cout << "Reflexivity: " << (reflexive_ok ? "PASS" : "FAIL") << "\n";
        assert(reflexive_ok && "Reflexivity check failed");

        // Check transitivity
        bool transitive_ok = true;
        for (int i = 0; i < ps && transitive_ok; ++i) {
            for (int j = 0; j < ps && transitive_ok; ++j) {
                for (int k = 0; k < ps && transitive_ok; ++k) {
                    if (matrix[i][j] && matrix[j][k] && !matrix[i][k]) {
                        transitive_ok = false;
                    }
                }
            }
        }
        std::cout << "Transitivity: " << (transitive_ok ? "PASS" : "FAIL") << "\n";
        assert(transitive_ok && "Transitivity check failed");
    }

    void verify_monotonicity(const std::vector<std::vector<bool>>& matrix) {
        int ps = vars.size();
        int n = vars.universe_size();
        bool monotonicity_ok = true;

        for (int i = 0; i < ps; ++i) {
            for (int j = 0; j < ps; ++j) {
                if (BitOps::is_subset(i, j) && !matrix[i][j]) {
                    monotonicity_ok = false;
                    std::cout << "Monotonicity violation: " 
                              << BitOps::to_string(i, n) << " ⊆ " 
                              << BitOps::to_string(j, n) 
                              << " but not " << i << " ≤ " << j << "\n";
                }
            }
        }
        std::cout << "Monotonicity: " << (monotonicity_ok ? "PASS" : "FAIL") << "\n";
        assert(monotonicity_ok && "Monotonicity check failed");
    }

    void verify_non_triviality(const std::vector<std::vector<bool>>& matrix) {
        int full_set = vars.size() - 1;
        int empty_set = 0;
        bool non_triviality_ok = !matrix[full_set][empty_set];

        std::cout << "Non-triviality: " << (non_triviality_ok ? "PASS" : "FAIL") << "\n";
        assert(non_triviality_ok && "Non-triviality check failed");
    }
};

// ============================================================
//  Main - Demonstration
// ============================================================

int main() {
    // Create finder for universe {0, 1, 2}
    int n = 5;
    FrameFinder finder(n);

    // Encode axioms by directly calling encoder methods
    std::cout << "\nEncoding axioms...\n";
    finder.encoder().encode_transitivity(finder.solver());
    finder.encoder().encode_monotonicity(finder.solver());
    finder.encoder().encode_non_triviality(finder.solver());

    // Solve
    z3::check_result result = finder.solve();

    if (result == z3::sat) {
        std::cout << "SAT - Solution found!\n";
        finder.display_model();
    } else if (result == z3::unsat) {
        std::cout << "UNSAT - No solution exists with given constraints\n";
    } else {
        std::cout << "UNKNOWN - Solver couldn't determine\n";
    }

    return 0;
}

