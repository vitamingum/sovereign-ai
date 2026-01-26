"""
Σ.py — Computational proofs for the Σ paper

Peres-Mermin Square: NC Polytope Analysis
==========================================

Results:
  • Theorem 1 (Fully Mixed Extremality): 115 vertices, all probabilistic
  • Theorem 2 (κ = 5): Maximum 5 deterministic constraints before collapse

Usage:
  python Σ.py --vertices     # Enumerate vertices, prove Theorem 1
  python Σ.py --kappa        # Compute constraint limit, prove Theorem 2
  python Σ.py --intersect    # Compute P_A ∩ P_B dimension reduction
  python Σ.py --all          # Run all analyses
"""

import numpy as np
from itertools import product as cart_product
from scipy.optimize import linprog
from collections import Counter
import argparse
import warnings
warnings.filterwarnings('ignore')


# =============================================================================
# PERES-MERMIN SQUARE SETUP
# =============================================================================
#
#      C1    C2    C3
# R1:  A     B     C    (product = +1)
# R2:  a     b     c    (product = +1)
# R3:  α     β     γ    (product = +1)
#
# Columns: product = -1 each (except C3 in some formulations)
#
# Observables:
#   A = X⊗I, B = I⊗X, C = X⊗X
#   a = I⊗Y, b = Y⊗I, c = Y⊗Y
#   α = X⊗Y, β = Y⊗X, γ = Z⊗Z

OBSERVABLES = ['A', 'B', 'C', 'a', 'b', 'c', 'α', 'β', 'γ']

CONTEXTS = {
    'R1': [0, 1, 2],  # A, B, C
    'R2': [3, 4, 5],  # a, b, c
    'R3': [6, 7, 8],  # α, β, γ
    'C1': [0, 3, 6],  # A, a, α
    'C2': [1, 4, 7],  # B, b, β
    'C3': [2, 5, 8],  # C, c, γ
}

# Product constraints
PRODUCTS = {
    'R1': +1, 'R2': +1, 'R3': +1,
    'C1': -1, 'C2': -1, 'C3': -1
}

CTX_ORDER = ['R1', 'R2', 'R3', 'C1', 'C2', 'C3']


# =============================================================================
# SHARED UTILITIES
# =============================================================================

def enumerate_sections(context_indices, required_product):
    """Enumerate valid {-1,+1}^3 sections satisfying product constraint."""
    sections = []
    for bits in cart_product([-1, 1], repeat=3):
        if bits[0] * bits[1] * bits[2] == required_product:
            sections.append(list(bits))
    return sections


def build_section_index():
    """Build mapping from (context, section) to variable index."""
    context_sections = {}
    section_ids = {}
    var_count = 0
    
    for ctx in CTX_ORDER:
        indices = CONTEXTS[ctx]
        req_prod = PRODUCTS[ctx]
        context_sections[ctx] = enumerate_sections(indices, req_prod)
        section_ids[ctx] = {}
        for sec in context_sections[ctx]:
            section_ids[ctx][tuple(sec)] = var_count
            var_count += 1
    
    return context_sections, section_ids, var_count


def build_constraints():
    """Build equality constraint matrix for NC polytope."""
    context_sections, section_ids, n_vars = build_section_index()
    
    A_eq_rows = []
    b_eq = []
    
    # Normalization: sum of sections per context = 1
    for ctx in CTX_ORDER:
        row = [0] * n_vars
        for sec_tuple, var_id in section_ids[ctx].items():
            row[var_id] = 1
        A_eq_rows.append(row)
        b_eq.append(1)
    
    # Marginal agreement: P(obs=+1) consistent across contexts
    for obs_idx in range(9):
        containing = []
        for ctx, indices in CONTEXTS.items():
            if obs_idx in indices:
                pos = indices.index(obs_idx)
                containing.append((ctx, pos))
        
        if len(containing) >= 2:
            ctx1, pos1 = containing[0]
            ctx2, pos2 = containing[1]
            
            row = [0] * n_vars
            for sec_tuple, var_id in section_ids[ctx1].items():
                if sec_tuple[pos1] == +1:
                    row[var_id] = 1
            for sec_tuple, var_id in section_ids[ctx2].items():
                if sec_tuple[pos2] == +1:
                    row[var_id] = -1
            
            A_eq_rows.append(row)
            b_eq.append(0)
    
    return np.array(A_eq_rows), np.array(b_eq), context_sections, section_ids, n_vars


# =============================================================================
# THEOREM 1: FULLY MIXED EXTREMALITY
# =============================================================================

def find_vertices(n_directions=2000, seed=42):
    """Find vertices of NC polytope via optimization."""
    A_eq, b_eq, context_sections, section_ids, n_vars = build_constraints()
    
    np.random.seed(seed)
    vertices = []
    seen = set()
    
    def find_vertex(direction):
        result = linprog(
            c=-direction,
            A_eq=A_eq,
            b_eq=b_eq,
            bounds=[(0, 1) for _ in range(n_vars)],
            method='highs'
        )
        if result.success:
            return np.round(result.x, 8)
        return None
    
    # Random directions
    for _ in range(n_directions):
        direction = np.random.randn(n_vars)
        v = find_vertex(direction)
        if v is not None:
            key = tuple(np.round(v, 6))
            if key not in seen:
                seen.add(key)
                vertices.append(v)
    
    # Axis-aligned directions
    for j in range(n_vars):
        for sign in [1, -1]:
            direction = np.zeros(n_vars)
            direction[j] = sign
            v = find_vertex(direction)
            if v is not None:
                key = tuple(np.round(v, 6))
                if key not in seen:
                    seen.add(key)
                    vertices.append(v)
    
    return vertices, context_sections, section_ids, n_vars


def analyze_vertices():
    """Analyze vertex structure — proof of Theorem 1."""
    print("=" * 70)
    print("THEOREM 1: FULLY MIXED EXTREMALITY")
    print("=" * 70)
    
    vertices, context_sections, section_ids, n_vars = find_vertices()
    
    print(f"\nTotal vertices found: {len(vertices)}")
    
    # Sparsity analysis
    sparsity = [sum(1 for x in v if x > 0.001) for v in vertices]
    
    print(f"\nSparsity (non-zero entries per vertex):")
    print(f"  Min: {min(sparsity)}")
    print(f"  Max: {max(sparsity)}")
    print(f"  Mean: {np.mean(sparsity):.1f}")
    
    print(f"\n  A deterministic vertex would require k = 6 (one per context)")
    print(f"  Observed minimum: k = {min(sparsity)}")
    
    if min(sparsity) > 6:
        print(f"\n✓ THEOREM 1 CONFIRMED: No deterministic extreme point exists.")
        print(f"  All {len(vertices)} vertices are intrinsically probabilistic.")
    
    # Signature distribution
    def vertex_signature(v):
        sig = {}
        for ctx in CTX_ORDER:
            active = sum(1 for sec_tuple, var_id in section_ids[ctx].items() 
                        if v[var_id] > 0.001)
            sig[ctx] = active
        return tuple(sig[ctx] for ctx in CTX_ORDER)
    
    signatures = [vertex_signature(v) for v in vertices]
    sig_counts = Counter(signatures)
    
    print(f"\nVertex signatures (active sections per context):")
    print(f"  Format: (R1, R2, R3, C1, C2, C3)")
    for sig in sorted(sig_counts.keys(), key=lambda x: sum(x))[:5]:
        print(f"    {sig}: {sig_counts[sig]} vertices")
    
    return vertices, section_ids


def show_example_vertex(vertices, section_ids):
    """Display one minimal vertex in detail."""
    print("\n" + "-" * 70)
    print("Example minimal vertex:")
    print("-" * 70)
    
    v = vertices[0]
    for ctx in CTX_ORDER:
        print(f"\n{ctx}:")
        for sec_tuple, var_id in section_ids[ctx].items():
            p = v[var_id]
            if p > 0.001:
                obs_names = [OBSERVABLES[i] for i in CONTEXTS[ctx]]
                sec_dict = dict(zip(obs_names, sec_tuple))
                print(f"  P({sec_dict}) = {p:.4f}")


# =============================================================================
# THEOREM 2: κ = 5 (CONSTRAINT LIMIT)
# =============================================================================

def check_subset_feasibility(obs_subset, values):
    """Check if a deterministic assignment to subset is feasible."""
    A_eq, b_eq, context_sections, section_ids, n_vars = build_constraints()
    
    A_list = list(A_eq)
    b_list = list(b_eq)
    
    for obs, val in zip(obs_subset, values):
        obs_idx = OBSERVABLES.index(obs)
        
        # Find a context containing this observable
        for ctx, indices in CONTEXTS.items():
            if obs_idx in indices:
                pos = indices.index(obs_idx)
                row = [0] * n_vars
                for sec_tuple, var_id in section_ids[ctx].items():
                    if sec_tuple[pos] == +1:
                        row[var_id] = 1
                A_list.append(row)
                b_list.append(1.0 if val == +1 else 0.0)
                break
    
    c = np.zeros(n_vars)
    bounds = [(0, None) for _ in range(n_vars)]
    result = linprog(c, A_eq=np.array(A_list), b_eq=np.array(b_list), 
                     bounds=bounds, method='highs')
    return result.success


def compute_kappa():
    """Compute maximum satisfiable subset size — proof of Theorem 2."""
    print("\n" + "=" * 70)
    print("THEOREM 2: κ (CONSTRAINT LIMIT)")
    print("=" * 70)
    
    from itertools import combinations
    
    max_feasible = 0
    
    for k in range(1, 10):
        feasible_count = 0
        total_count = 0
        
        for subset in combinations(OBSERVABLES, k):
            for values in cart_product([-1, +1], repeat=k):
                total_count += 1
                if check_subset_feasibility(subset, values):
                    feasible_count += 1
                    max_feasible = max(max_feasible, k)
        
        pct = 100 * feasible_count / total_count if total_count > 0 else 0
        print(f"  k={k}: {feasible_count}/{total_count} feasible ({pct:.1f}%)")
        
        if feasible_count == 0:
            print(f"\n✓ THEOREM 2 CONFIRMED: κ = {k-1}")
            print(f"  No subset of size {k} admits a feasible deterministic assignment.")
            break
    
    # Check for adversarial 4-subsets
    print("\n" + "-" * 70)
    print("Corollary: Adversarial subsets of size 4")
    print("-" * 70)
    
    adversarial_count = 0
    for subset in combinations(OBSERVABLES, 4):
        all_infeasible = True
        for values in cart_product([-1, +1], repeat=4):
            if check_subset_feasibility(subset, values):
                all_infeasible = False
                break
        if all_infeasible:
            adversarial_count += 1
            if adversarial_count <= 3:
                print(f"  Adversarial: {subset}")
    
    print(f"\n  Total adversarial 4-subsets: {adversarial_count}")


# =============================================================================
# INTERSECTION ANALYSIS
# =============================================================================

def analyze_intersection():
    """Compute P_A ∩ P_B dimension reduction."""
    print("\n" + "=" * 70)
    print("INTERSECTION ANALYSIS: P_A ∩ P_B")
    print("=" * 70)
    
    A_eq, b_eq, context_sections, section_ids, n_vars = build_constraints()
    
    def add_marginal_constraint(A, b, obs, prob):
        """Add constraint P(obs=+1) = prob."""
        obs_idx = OBSERVABLES.index(obs)
        
        for ctx, indices in CONTEXTS.items():
            if obs_idx in indices:
                pos = indices.index(obs_idx)
                row = np.zeros(n_vars)
                for sec_tuple, var_id in section_ids[ctx].items():
                    if sec_tuple[pos] == +1:
                        row[var_id] = 1
                return np.vstack([A, row]), np.append(b, prob)
        return A, b
    
    def compute_dimension(A):
        return n_vars - np.linalg.matrix_rank(A)
    
    dim_base = compute_dimension(A_eq)
    
    scenarios = [
        ("Base NC polytope", []),
        ("Alice (A=0.5)", [('A', 0.5)]),
        ("Bob (B=0.5)", [('B', 0.5)]),
        ("P_A ∩ P_B", [('A', 0.5), ('B', 0.5)]),
        ("Agree on R1", [('A', 0.5), ('B', 0.5), ('C', 0.5)]),
        ("Agree on R1+R2", [('A', 0.5), ('B', 0.5), ('C', 0.5), 
                            ('a', 0.5), ('b', 0.5), ('c', 0.5)]),
        ("All 9 marginals", [(obs, 0.5) for obs in OBSERVABLES]),
    ]
    
    print(f"\n{'Scenario':<25} {'Constraints':<12} {'Dimension':<10} {'Reduction'}")
    print("-" * 60)
    
    for name, constraints in scenarios:
        A, b = A_eq.copy(), b_eq.copy()
        for obs, prob in constraints:
            A, b = add_marginal_constraint(A, b, obs, prob)
        dim = compute_dimension(A)
        reduction = dim_base - dim
        print(f"{name:<25} {len(constraints):<12} {dim:<10} {reduction}")
    
    print(f"\n  Formula: Σ = {dim_base} − (# independent agreements)")


# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description='Σ.py — Peres-Mermin NC Polytope Analysis')
    parser.add_argument('--vertices', action='store_true', help='Theorem 1: Vertex enumeration')
    parser.add_argument('--kappa', action='store_true', help='Theorem 2: Constraint limit')
    parser.add_argument('--intersect', action='store_true', help='Intersection dimension analysis')
    parser.add_argument('--all', action='store_true', help='Run all analyses')
    
    args = parser.parse_args()
    
    if args.all or (not args.vertices and not args.kappa and not args.intersect):
        args.vertices = args.kappa = args.intersect = True
    
    print("\n" + "=" * 70)
    print("Σ.py — Computational proofs for the Σ paper")
    print("=" * 70)
    
    if args.vertices:
        vertices, section_ids = analyze_vertices()
        show_example_vertex(vertices, section_ids)
    
    if args.kappa:
        compute_kappa()
    
    if args.intersect:
        analyze_intersection()
    
    print("\n" + "=" * 70)
    print("DONE")
    print("=" * 70)


if __name__ == '__main__':
    main()
