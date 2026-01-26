"""
Certificate Generator for κ=5 Lean Proof
Generated via 互照 fusion: gemini + gpt52 + opus | 2026-01-26

This script:
1. Builds the NC polytope constraints for each size-6 subset
2. Solves for infeasibility using LP (scipy/cvxpy)
3. Extracts Farkas dual certificates
4. Rationalizes floats to exact fractions
5. Emits Lean-compatible certificate data
"""

from fractions import Fraction
from itertools import combinations, product
from typing import List, Tuple, Dict, Optional
import numpy as np

# Try to import scipy for LP solving
try:
    from scipy.optimize import linprog
    HAS_SCIPY = True
except ImportError:
    HAS_SCIPY = False
    print("Warning: scipy not available. Install with: pip install scipy")


# =============================================================================
# PERES-MERMIN STRUCTURE
# =============================================================================

CONTEXTS = [
    [0, 1, 2],  # row 0
    [3, 4, 5],  # row 1
    [6, 7, 8],  # row 2
    [0, 3, 6],  # col 0
    [1, 4, 7],  # col 1
    [2, 5, 8],  # col 2
]

PARITIES = [1, 1, 1, 1, 1, -1]  # product constraint per context

def get_sections(parity: int) -> List[Tuple[int, int, int]]:
    """Get 4 local assignments satisfying parity constraint."""
    if parity == 1:
        return [(-1, -1, -1), (-1, 1, 1), (1, -1, 1), (1, 1, -1)]
    else:
        return [(-1, -1, 1), (-1, 1, -1), (1, -1, -1), (1, 1, 1)]


# =============================================================================
# CONSTRAINT BUILDING
# =============================================================================

def build_constraints(
    subset: List[int],
    values: Dict[int, int]
) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """
    Build LP constraints for NC polytope with deterministic values.
    
    Returns: A_eq, b_eq, A_ub, b_ub for the LP:
        A_eq @ x = b_eq
        A_ub @ x <= b_ub
        x >= 0
    """
    n_vars = 24  # 6 contexts × 4 sections
    
    eq_constraints = []  # (coeffs, rhs)
    
    # 1. NORMALIZATION: Σ_s p[c,s] = 1 for each context
    for c in range(6):
        row = [0.0] * n_vars
        for s in range(4):
            row[c * 4 + s] = 1.0
        eq_constraints.append((row, 1.0))
    
    # 2. MARGINAL CONSISTENCY: overlapping observables
    # For each observable that appears in 2 contexts, marginals must match
    for obs in range(9):
        contexts_with_obs = []
        for c, ctx in enumerate(CONTEXTS):
            if obs in ctx:
                pos = ctx.index(obs)
                contexts_with_obs.append((c, pos))
        
        if len(contexts_with_obs) == 2:
            (c1, pos1), (c2, pos2) = contexts_with_obs
            sections1 = get_sections(PARITIES[c1])
            sections2 = get_sections(PARITIES[c2])
            
            # For each value v in {-1, +1}:
            # Σ_{s: section[pos]=v} p[c1,s] = Σ_{s: section[pos]=v} p[c2,s]
            for v in [-1, 1]:
                row = [0.0] * n_vars
                for s, sec in enumerate(sections1):
                    if sec[pos1] == v:
                        row[c1 * 4 + s] = 1.0
                for s, sec in enumerate(sections2):
                    if sec[pos2] == v:
                        row[c2 * 4 + s] = -1.0
                # Only add if non-trivial
                if any(r != 0 for r in row):
                    eq_constraints.append((row, 0.0))
    
    # 3. DETERMINISM: for fixed observables, force marginal = 1 or 0
    for obs in subset:
        val = values[obs]
        for c, ctx in enumerate(CONTEXTS):
            if obs in ctx:
                pos = ctx.index(obs)
                sections = get_sections(PARITIES[c])
                
                # Σ_{s: section[pos]=val} p[c,s] = 1
                row = [0.0] * n_vars
                for s, sec in enumerate(sections):
                    if sec[pos] == val:
                        row[c * 4 + s] = 1.0
                eq_constraints.append((row, 1.0))
    
    # Build matrices
    if eq_constraints:
        A_eq = np.array([c[0] for c in eq_constraints])
        b_eq = np.array([c[1] for c in eq_constraints])
    else:
        A_eq = np.zeros((0, n_vars))
        b_eq = np.zeros(0)
    
    # No inequality constraints beyond x >= 0 (handled by bounds)
    A_ub = np.zeros((0, n_vars))
    b_ub = np.zeros(0)
    
    return A_eq, b_eq, A_ub, b_ub


def check_feasibility(subset: List[int], values: Dict[int, int]) -> Tuple[bool, Optional[np.ndarray]]:
    """
    Check if the NC polytope is feasible for given subset and values.
    Returns (is_feasible, dual_certificate_if_infeasible).
    """
    if not HAS_SCIPY:
        return True, None  # Can't check without scipy
    
    A_eq, b_eq, _, _ = build_constraints(subset, values)
    n_vars = 24
    
    # Solve feasibility LP: min 0 s.t. A_eq @ x = b_eq, x >= 0
    c = np.zeros(n_vars)
    bounds = [(0, None)] * n_vars
    
    result = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')
    
    if result.success:
        return True, None
    else:
        # Infeasible - try to extract dual certificate
        # The dual is in result.eqlin.marginals for equality constraints
        # But we need to be careful about the format
        return False, None  # TODO: extract proper Farkas dual


def rationalize(x: float, max_denom: int = 1000000) -> Tuple[int, int]:
    """Convert float to (numerator, denominator) pair."""
    frac = Fraction(x).limit_denominator(max_denom)
    return (frac.numerator, frac.denominator)


# =============================================================================
# LEAN CODE GENERATION
# =============================================================================

def emit_lean_certificate(
    subset: List[int],
    values: Dict[int, int],
    y: np.ndarray,
    A: np.ndarray,
    b: np.ndarray
) -> str:
    """Generate Lean code for a single infeasibility certificate."""
    m, n = A.shape
    
    lines = []
    lines.append(f"-- Subset: {subset}, Values: {values}")
    
    # Emit A as sparse function
    lines.append(f"def A_{hash(tuple(subset)) % 10000} : Fin {m} → Fin {n} → Int × Int")
    lines.append("  | i, j => match (i.val, j.val) with")
    for i in range(m):
        for j in range(n):
            if A[i, j] != 0:
                num, den = rationalize(A[i, j])
                lines.append(f"    | ({i}, {j}) => ({num}, {den})")
    lines.append("    | _ => (0, 1)")
    
    # Emit b
    lines.append(f"def b_{hash(tuple(subset)) % 10000} : Fin {m} → Int × Int")
    lines.append("  | i => match i.val with")
    for i in range(m):
        num, den = rationalize(b[i])
        lines.append(f"    | {i} => ({num}, {den})")
    lines.append("    | _ => (0, 1)")
    
    # Emit y (dual certificate)
    lines.append(f"def y_{hash(tuple(subset)) % 10000} : Fin {m} → Int × Int")
    lines.append("  | i => match i.val with")
    for i in range(m):
        if y[i] != 0:
            num, den = rationalize(y[i])
            lines.append(f"    | {i} => ({num}, {den})")
    lines.append("    | _ => (0, 1)")
    
    return "\n".join(lines)


# =============================================================================
# MAIN
# =============================================================================

def main():
    """Generate all certificates for κ=5 proof."""
    
    print("=== κ=5 Certificate Generator ===")
    print()
    
    # Test with one small case first
    subset = [0, 1, 2, 3, 4, 5]  # First 6 observables
    values = {0: 1, 1: 1, 2: 1, 3: 1, 4: 1, 5: 1}
    
    print(f"Testing subset {subset} with all +1 values...")
    
    A_eq, b_eq, _, _ = build_constraints(subset, values)
    print(f"  Constraints: {A_eq.shape[0]} equations, {A_eq.shape[1]} variables")
    
    is_feas, dual = check_feasibility(subset, values)
    print(f"  Feasible: {is_feas}")
    
    if not is_feas and dual is not None:
        print(f"  Dual certificate found")
    
    # TODO: Full enumeration and certificate extraction
    # This requires a proper LP solver with dual access (cvxpy + ECOS/SCS)
    
    print()
    print("To complete: install cvxpy and implement dual extraction")
    print("  pip install cvxpy")


if __name__ == "__main__":
    main()
