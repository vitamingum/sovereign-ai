"""
Σ_certificates.py — Farkas Certificate Generator for κ=5 Proof

This script generates Farkas witnesses (dual certificates) proving
that no probability distribution over NC polytope sections can have
deterministic marginals on subsets of size 6.

Architecture:
  Python: Solves LPs, extracts dual certificates
  Lean:   Verifies certificates via rational arithmetic

Output: JSON certificates for each infeasible (subset, assignment) pair
"""

import numpy as np
from scipy.optimize import linprog
from itertools import combinations, product as cart_product
import json
from fractions import Fraction
import argparse

# =============================================================================
# PERES-MERMIN SETUP (mirrors Σ.py)
# =============================================================================

OBSERVABLES = ['A', 'B', 'C', 'a', 'b', 'c', 'α', 'β', 'γ']

CONTEXTS = {
    'R1': [0, 1, 2],
    'R2': [3, 4, 5],
    'R3': [6, 7, 8],
    'C1': [0, 3, 6],
    'C2': [1, 4, 7],
    'C3': [2, 5, 8],
}

PRODUCTS = {
    'R1': +1, 'R2': +1, 'R3': +1,
    'C1': -1, 'C2': -1, 'C3': -1
}

CTX_ORDER = ['R1', 'R2', 'R3', 'C1', 'C2', 'C3']


def enumerate_sections(required_product):
    """Enumerate valid {-1,+1}^3 sections satisfying product constraint."""
    sections = []
    for bits in cart_product([-1, 1], repeat=3):
        if bits[0] * bits[1] * bits[2] == required_product:
            sections.append(list(bits))
    return sections


def build_full_constraint_system():
    """
    Build the NC polytope constraint matrix.
    MATCHES Σ.py EXACTLY.
    
    Variables: p_{ctx, sec} for each (context, section) pair
    Total: 6 contexts × 4 sections = 24 variables
    
    Constraints:
    1. Normalization: sum over sections in each context = 1
    2. Marginal agreement: P(obs=+1) consistent across contexts
    3. Non-negativity: all p >= 0
    """
    # Build section index
    context_sections = {}
    section_ids = {}
    var_to_ctx_sec = []
    var_count = 0
    
    for ctx in CTX_ORDER:
        req_prod = PRODUCTS[ctx]
        context_sections[ctx] = enumerate_sections(req_prod)
        section_ids[ctx] = {}
        for sec in context_sections[ctx]:
            section_ids[ctx][tuple(sec)] = var_count
            var_to_ctx_sec.append((ctx, tuple(sec)))
            var_count += 1
    
    n_vars = var_count  # Should be 24
    
    A_eq_rows = []
    b_eq = []
    
    # Normalization constraints (6 equations)
    for ctx in CTX_ORDER:
        row = [0] * n_vars
        for sec_tuple, var_id in section_ids[ctx].items():
            row[var_id] = 1
        A_eq_rows.append(row)
        b_eq.append(1)
    
    # Marginal agreement: P(obs=+1) consistent across contexts
    for obs_idx in range(9):
        containing = []
        for ctx in CTX_ORDER:
            if obs_idx in CONTEXTS[ctx]:
                pos = CONTEXTS[ctx].index(obs_idx)
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
    
    return np.array(A_eq_rows), np.array(b_eq), context_sections, section_ids, var_to_ctx_sec, n_vars


def add_deterministic_constraints(A_eq, b_eq, context_sections, section_ids, var_to_ctx_sec, 
                                   obs_indices, values):
    """
    Add constraints forcing specific observables to have deterministic values.
    MATCHES Σ.py EXACTLY.
    
    For observable i with value v in {-1, +1}:
      The marginal constraint is:
      sum of p_{ctx, sec} where sec[pos] == +1 equals 1 if v == +1, else 0
      
    We add this constraint for ONE context containing each observable.
    """
    n_vars = len(var_to_ctx_sec)
    A_list = list(A_eq)
    b_list = list(b_eq)
    
    for obs_idx, val in zip(obs_indices, values):
        # Find ONE context containing this observable (first match)
        for ctx in CTX_ORDER:
            if obs_idx in CONTEXTS[ctx]:
                pos = CONTEXTS[ctx].index(obs_idx)
                
                # Constraint: sum of p_{ctx, sec} where sec[pos] == +1
                row = [0] * n_vars
                for sec_tuple, var_id in section_ids[ctx].items():
                    if sec_tuple[pos] == +1:
                        row[var_id] = 1
                
                A_list.append(row)
                b_list.append(1.0 if val == +1 else 0.0)
                break  # Only use first context, matching Σ.py
    
    return np.array(A_list), np.array(b_list)


def check_feasibility_with_certificate(obs_indices, values):
    """
    Check if deterministic assignment is feasible.
    If infeasible, return a Farkas certificate.
    
    Farkas Lemma:
      Ax = b, x >= 0 is infeasible
      iff
      ∃ y such that y^T A >= 0 and y^T b < 0
    """
    A_eq_base, b_eq_base, context_sections, section_ids, var_to_ctx_sec, n_vars = \
        build_full_constraint_system()
    
    A_eq, b_eq = add_deterministic_constraints(
        A_eq_base, b_eq_base, context_sections, section_ids, var_to_ctx_sec,
        obs_indices, values
    )
    
    # Solve feasibility LP
    c = np.zeros(n_vars)
    bounds = [(0, None) for _ in range(n_vars)]
    
    result = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')
    
    if result.success:
        return True, None  # Feasible
    
    # Extract Farkas certificate from dual
    # The HiGHS solver provides marginals when infeasible
    if hasattr(result, 'ineqlin') and result.ineqlin is not None:
        # Certificate is the dual variables
        y = result.eqlin.marginals if hasattr(result, 'eqlin') else None
        if y is not None:
            # Convert to rationals for exact verification
            y_rat = [str(Fraction(float(yi)).limit_denominator(10000)) 
                     for yi in y]
            return False, {
                'dual': y_rat,
                'A_eq': A_eq.tolist(),
                'b_eq': b_eq.tolist()
            }
    
    # Fallback: just mark as infeasible without certificate
    return False, {'status': 'infeasible', 'solver_message': result.message}


def generate_certificates(k=6, output_file='certificates.json'):
    """Generate certificates for all infeasible size-k subsets."""
    
    print(f"Generating certificates for size-{k} subsets...")
    
    certificates = {
        'k': k,
        'total_subsets': 0,
        'infeasible_count': 0,
        'feasible_count': 0,
        'cases': []
    }
    
    for subset in combinations(range(9), k):
        for values in cart_product([-1, +1], repeat=k):
            certificates['total_subsets'] += 1
            
            feasible, cert = check_feasibility_with_certificate(
                list(subset), list(values)
            )
            
            if feasible:
                certificates['feasible_count'] += 1
            else:
                certificates['infeasible_count'] += 1
                certificates['cases'].append({
                    'subset': list(subset),
                    'values': list(values),
                    'certificate': cert
                })
    
    print(f"Total cases: {certificates['total_subsets']}")
    print(f"Infeasible: {certificates['infeasible_count']}")
    print(f"Feasible: {certificates['feasible_count']}")
    
    with open(output_file, 'w') as f:
        json.dump(certificates, f, indent=2)
    
    print(f"Certificates written to {output_file}")
    
    return certificates


def main():
    parser = argparse.ArgumentParser(description='Generate Farkas certificates for κ=5 proof')
    parser.add_argument('--size', type=int, default=6, help='Subset size to check')
    parser.add_argument('--output', type=str, default='certificates.json', help='Output file')
    args = parser.parse_args()
    
    generate_certificates(k=args.size, output_file=args.output)


if __name__ == '__main__':
    main()
