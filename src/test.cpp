#include <iostream>
#include <vector>
#include <string>
#include <sstream>
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
//  Partial Preorder Finder
// ============================================================
//  Find a partial preorder relation over the powerset P(Omega)
//  represented as a boolean matrix R[i][j] where i,j are bitmasks
// ============================================================

class PartialPreorderFinder {
    z3::context& ctx;
    int n;              // Universe size
    int powerset_size;  // 2^n subsets
    std::vector<std::vector<z3::expr>> R;  // R[i][j] = (subset_i ≤ subset_j)
    
public:
    PartialPreorderFinder(z3::context& c, int universe_size) 
        : ctx(c), n(universe_size), powerset_size(1 << universe_size) {
        
        std::cout << "Creating partial preorder finder for universe size " << n << "\n";
        std::cout << "Powerset has " << powerset_size << " subsets\n";
        
        // Step 1: CREATE FREE VARIABLES - Boolean matrix R[i][j]
        for (int i = 0; i < powerset_size; ++i) {
            R.emplace_back();
            for (int j = 0; j < powerset_size; ++j) {
                std::string var_name = "R_" + std::to_string(i) + "_" + std::to_string(j);
                R[i].push_back(ctx.bool_const(var_name.c_str()));
            }
        }
        std::cout << "Created " << (powerset_size * powerset_size) << " boolean variables\n";
    }
    
    // Step 2: ENCODE PARTIAL PREORDER AXIOMS
    void add_preorder_axioms(z3::solver& s) {
        std::cout << "\nEncoding partial preorder axioms...\n";
        
        // AXIOM 1: Reflexivity - every subset is related to itself
        std::cout << "  Adding reflexivity constraints...\n";
        for (int i = 0; i < powerset_size; ++i) {
            s.add(R[i][i]);  // R[i][i] = true
        }
        
        // AXIOM 2: Transitivity - if i ≤ j and j ≤ k, then i ≤ k
        std::cout << "  Adding transitivity constraints...\n";
        int trans_count = 0;
        for (int i = 0; i < powerset_size; ++i) {
            for (int j = 0; j < powerset_size; ++j) {
                for (int k = 0; k < powerset_size; ++k) {
                    // (R[i][j] ∧ R[j][k]) → R[i][k]
                    s.add(z3::implies(R[i][j] && R[j][k], R[i][k]));
                    trans_count++;
                }
            }
        }
        std::cout << "  Added " << trans_count << " transitivity implications\n";
    }
    
    // Optional: Monotonicity - subset inclusion implies ordering
    void add_monotonicity(z3::solver& s) {
        std::cout << "  Adding monotonicity (subset inclusion → ordering)...\n";
        for (int i = 0; i < powerset_size; ++i) {
            for (int j = 0; j < powerset_size; ++j) {
                if (BitOps::is_subset(i, j)) {
                    s.add(R[i][j]);  // i ⊆ j → i ≤ j
                }
            }
        }
    }
    
    // Optional: Require non-trivial ordering (not just equality)
    void require_nontrivial(z3::solver& s) {
        std::cout << "  Requiring non-trivial ordering...\n";
        z3::expr_vector has_strict_order(ctx);
        
        for (int i = 0; i < powerset_size; ++i) {
            for (int j = 0; j < powerset_size; ++j) {
                if (i != j) {
                    // At least one strict ordering: i ≤ j but not j ≤ i
                    has_strict_order.push_back(R[i][j] && !R[j][i]);
                }
            }
        }
        s.add(z3::mk_or(has_strict_order));
    }
    
    // Step 4: EXTRACT & DISPLAY MODEL
    void display_model(z3::model& m) {
        std::cout << "\n=== PARTIAL PREORDER FOUND ===\n\n";
        
        // Extract boolean matrix
        std::vector<std::vector<bool>> matrix(powerset_size, std::vector<bool>(powerset_size));
        for (int i = 0; i < powerset_size; ++i) {
            for (int j = 0; j < powerset_size; ++j) {
                matrix[i][j] = m.eval(R[i][j]).is_true();
            }
        }
        
        // Display full matrix
        display_matrix(matrix);
        
        // // Display comparable pairs
        // display_comparable_pairs(matrix);
        
        // // Display covering relations (Hasse diagram edges)
        // display_covering_relations(matrix);
        
        // Verify it's a valid preorder
        verify_preorder(matrix);
    }
    
private:
    void display_matrix(const std::vector<std::vector<bool>>& matrix) {
        std::cout << "Boolean Matrix R[i][j] (1 means subset_i ≤ subset_j):\n\n";
        std::cout << "     ";
        for (int j = 0; j < powerset_size; ++j) {
            std::cout << " " << j;
            if (j < 10) std::cout << " ";
        }
        std::cout << "\n     ";
        for (int j = 0; j < powerset_size; ++j) std::cout << "---";
        std::cout << "\n";
        
        for (int i = 0; i < powerset_size; ++i) {
            std::cout << " " << i;
            if (i < 10) std::cout << " ";
            std::cout << " | ";
            for (int j = 0; j < powerset_size; ++j) {
                std::cout << (matrix[i][j] ? "1" : "·") << "  ";
            }
            std::cout << " | " << BitOps::to_string(i, n) << "\n";
        }
    }
    
    // void display_comparable_pairs(const std::vector<std::vector<bool>>& matrix) {
    //     std::cout << "\nComparable pairs (i ≤ j):\n";
    //     int count = 0;
    //     for (int i = 0; i < powerset_size; ++i) {
    //         for (int j = 0; j < powerset_size; ++j) {
    //             if (matrix[i][j] && i != j) {
    //                 std::cout << "  " << BitOps::to_string(i, n) 
    //                           << " ≤ " << BitOps::to_string(j, n) << "\n";
    //                 count++;
    //             }
    //         }
    //     }
    //     std::cout << "Total: " << count << " strict orderings\n";
    // }
    
    // void display_covering_relations(const std::vector<std::vector<bool>>& matrix) {
    //     std::cout << "\nCovering relations (Hasse diagram edges):\n";
    //     // i covers j if i ≤ j and no k exists with i ≤ k ≤ j
    //     for (int i = 0; i < powerset_size; ++i) {
    //         for (int j = 0; j < powerset_size; ++j) {
    //             if (i != j && matrix[i][j]) {
    //                 bool is_covering = true;
    //                 for (int k = 0; k < powerset_size; ++k) {
    //                     if (k != i && k != j && matrix[i][k] && matrix[k][j]) {
    //                         is_covering = false;
    //                         break;
    //                     }
    //                 }
    //                 if (is_covering) {
    //                     std::cout << "  " << BitOps::to_string(i, n) 
    //                               << " ⋖ " << BitOps::to_string(j, n) << "\n";
    //                 }
    //             }
    //         }
    //     }
    // }
    
    void verify_preorder(const std::vector<std::vector<bool>>& matrix) {
        std::cout << "\n=== VERIFICATION ===\n";
        
        // Check reflexivity
        bool reflexive_ok = true;
        for (int i = 0; i < powerset_size; ++i) {
            if (!matrix[i][i]) {
                reflexive_ok = false;
                break;
            }
        }
        std::cout << "✓ Reflexivity: " << (reflexive_ok ? "PASS" : "FAIL") << "\n";
        
        // Check transitivity
        bool transitive_ok = true;
        for (int i = 0; i < powerset_size && transitive_ok; ++i) {
            for (int j = 0; j < powerset_size && transitive_ok; ++j) {
                for (int k = 0; k < powerset_size && transitive_ok; ++k) {
                    if (matrix[i][j] && matrix[j][k] && !matrix[i][k]) {
                        transitive_ok = false;
                    }
                }
            }
        }
        std::cout << "✓ Transitivity: " << (transitive_ok ? "PASS" : "FAIL") << "\n";
    }
};

// ============================================================
//  Main - Demonstration
// ============================================================

int main() {
    z3::context ctx;
    z3::solver s(ctx);
    
    // Find a partial preorder over P({0,1,2})
    int n = 3;
    PartialPreorderFinder finder(ctx, n);
    
    // Add core axioms
    finder.add_preorder_axioms(s);
    finder.add_monotonicity(s);      // Respect subset inclusion
    finder.require_nontrivial(s);    // Not just equality
    
    // Solve
    std::cout << "\nSearching for a partial preorder...\n";
    z3::check_result result = s.check();
    
    if (result == z3::sat) {
        std::cout << "SAT - Partial preorder found!\n";
        z3::model m = s.get_model();
        finder.display_model(m);
    } else if (result == z3::unsat) {
        std::cout << "UNSAT - No such partial preorder exists with given constraints\n";
    } else {
        std::cout << "UNKNOWN - Solver couldn't determine\n";
    }
    
    return 0;
}
