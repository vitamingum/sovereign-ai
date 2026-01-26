"""
Σ_lean_certs.py — Generate Lean-compatible Farkas certificates for κ=5

Architecture (per GPT council 2026-01-26):
  Python proposes: solve LPs, emit Farkas certificates over ℚ
  Lean verifies: check yᵀA ≥ 0 ∧ yᵀb < 0 via native_decide

Certificate form for infeasibility of {Ax = b, x ≥ 0}:
  y such that yᵀA ≥ 0 and yᵀb < 0  (Farkas alternative)
"""

import numpy as np
from scipy.optimize import linprog
from itertools import combinations, product as cart_product
from fractions import Fraction
import json
import sys

# =============================================================================
# PERES-MERMIN SETUP (mirrors Σ.py exactly)
# =============================================================================

CONTEXTS = {
    'R1': [0, 1, 2],
    'R2': [3, 4, 5],
    'R3': [6, 7, 8],
    'C1': [0, 3, 6],
    'C2': [1, 4, 7],
    'C3': [2, 5, 8],
}

PRODUCTS = {'R1': +1, 'R2': +1, 'R3': +1, 'C1': -1, 'C2': -1, 'C3': -1}
CTX_ORDER = ['R1', 'R2', 'R3', 'C1', 'C2', 'C3']

def sections_for(ctx):
    """4 sections per context, each satisfying parity constraint."""
    req = PRODUCTS[ctx]
    return [list(b) for b in cart_product([-1, 1], repeat=3) if b[0]*b[1]*b[2] == req]

# Variable indexing: x[i] for i in 0..23
# ctx_idx * 4 + sec_idx within that context
VAR_MAP = {}  # (ctx, sec_tuple) -> var_id
for ctx_idx, ctx in enumerate(CTX_ORDER):
    for sec_idx, sec in enumerate(sections_for(ctx)):
        VAR_MAP[(ctx, tuple(sec))] = ctx_idx * 4 + sec_idx

N_VARS = 24

# =============================================================================
# CONSTRAINT SYSTEM
# =============================================================================

def build_base_constraints():
    """
    Build base NC polytope as Ax = b system.
    Returns A (list of rows), b (list of RHS values).
    
    Constraints:
      - 6 normalization: sum of probs in each context = 1
      - 9 marginal agreement: P(obs=+1|ctx1) = P(obs=+1|ctx2)
    """
    A, b = [], []
    
    # Normalization (6 equations)
    for ctx_idx, ctx in enumerate(CTX_ORDER):
        row = [0] * N_VARS
        for sec in sections_for(ctx):
            row[VAR_MAP[(ctx, tuple(sec))]] = 1
        A.append(row)
        b.append(Fraction(1))
    
    # Marginal agreement (9 equations, one per observable)
    for obs in range(9):
        ctxs_with_obs = [(ctx, CONTEXTS[ctx].index(obs)) 
                         for ctx in CTX_ORDER if obs in CONTEXTS[ctx]]
        if len(ctxs_with_obs) >= 2:
            (ctx1, pos1), (ctx2, pos2) = ctxs_with_obs[0], ctxs_with_obs[1]
            row = [Fraction(0)] * N_VARS
            for sec in sections_for(ctx1):
                if sec[pos1] == +1:
                    row[VAR_MAP[(ctx1, tuple(sec))]] += 1
            for sec in sections_for(ctx2):
                if sec[pos2] == +1:
                    row[VAR_MAP[(ctx2, tuple(sec))]] -= 1
            A.append([Fraction(x) for x in row])
            b.append(Fraction(0))
    
    return A, b


def add_deterministic_constraints(A_base, b_base, obs_subset, values):
    """
    Add deterministic marginal constraints: P(obs=val) = 1.
    For val=+1: sum of sections where obs=+1 = 1
    For val=-1: sum of sections where obs=+1 = 0
    
    Only adds constraint for ONE context containing the observable
    (the constraints are redundant due to marginal agreement).
    """
    A = [row[:] for row in A_base]
    b = b_base[:]
    
    for obs, val in zip(obs_subset, values):
        # Find first context containing this observable
        for ctx in CTX_ORDER:
            if obs in CONTEXTS[ctx]:
                pos = CONTEXTS[ctx].index(obs)
                row = [Fraction(0)] * N_VARS
                for sec in sections_for(ctx):
                    if sec[pos] == +1:
                        row[VAR_MAP[(ctx, tuple(sec))]] = Fraction(1)
                A.append(row)
                b.append(Fraction(1) if val == +1 else Fraction(0))
                break
    
    return A, b


def find_farkas_certificate(A, b):
    """
    Find Farkas certificate for infeasibility of {Ax = b, x ≥ 0}.
    
    Farkas alternative: ∃y: yᵀA ≥ 0 and yᵀb < 0
    
    We use phase-1 simplex: min Σsᵢ s.t. Ax + s = b, x,s ≥ 0
    If optimal > 0, system is infeasible.
    The negated dual marginals give the Farkas certificate.
    """
    A_np = np.array([[float(x) for x in row] for row in A])
    b_np = np.array([float(x) for x in b])
    m, n = A_np.shape
    
    # Phase 1: min Σs s.t. [A | I][x; s] = b, x,s ≥ 0
    c_phase1 = np.concatenate([np.zeros(n), np.ones(m)])
    A_eq = np.concatenate([A_np, np.eye(m)], axis=1)
    
    res = linprog(c_phase1, A_eq=A_eq, b_eq=b_np, bounds=(0, None), method='highs')
    
    if res.success and res.fun > 1e-9:
        # Infeasible! Dual marginals (negated) give certificate
        if hasattr(res, 'eqlin') and res.eqlin is not None:
            marginals = res.eqlin.marginals
            y = -marginals  # Negate to get y^T b < 0
            
            # Verify
            yTA = y @ A_np
            yTb = y @ b_np
            if np.all(yTA >= -1e-9) and yTb < -1e-9:
                return y
    
    return None


def rationalize(y, A, b, max_denom=10000):
    """
    Convert certificate to exact rationals and verify.
    Scale to clear denominators for cleaner Lean representation.
    """
    y_rat = [Fraction(yi).limit_denominator(max_denom) for yi in y]
    
    # Verify: yᵀA ≥ 0 and yᵀb < 0
    yTA = [sum(y_rat[i] * A[i][j] for i in range(len(y_rat))) for j in range(N_VARS)]
    yTb = sum(y_rat[i] * b[i] for i in range(len(y_rat)))
    
    if all(x >= 0 for x in yTA) and yTb < 0:
        return y_rat
    
    # Try higher precision
    y_rat = [Fraction(yi).limit_denominator(1000000) for yi in y]
    yTA = [sum(y_rat[i] * A[i][j] for i in range(len(y_rat))) for j in range(N_VARS)]
    yTb = sum(y_rat[i] * b[i] for i in range(len(y_rat)))
    
    if all(x >= 0 for x in yTA) and yTb < 0:
        return y_rat
    
    return None


# =============================================================================
# LEAN CODE GENERATION
# =============================================================================

def frac_to_lean(f):
    """Format Fraction as Lean rational literal."""
    if f.denominator == 1:
        return str(f.numerator)
    return f"({f.numerator}/{f.denominator})"


def generate_lean_file():
    """Generate complete Lean 4 file with κ=5 proof."""
    
    A_base, b_base = build_base_constraints()
    
    lines = []
    lines.append("/-!")
    lines.append("# κ = 5 Formal Proof via Farkas Certificates")
    lines.append("")
    lines.append("Generated by Σ_lean_certs.py")
    lines.append("Architecture: Python solves LPs → emits certificates → Lean verifies")
    lines.append("")
    lines.append("Theorem: κ = 5 for the Peres-Mermin square")
    lines.append("  (A) κ ≤ 5: All size-6 deterministic assignments are NC-infeasible")
    lines.append("  (B) κ ≥ 5: At least one size-5 assignment is NC-feasible")
    lines.append("-/")
    lines.append("")
    lines.append("-- Rational arithmetic, decidable")
    lines.append("def Q := Int × Int  -- (num, denom), denom > 0")
    lines.append("")
    lines.append("def qmul (a b : Q) : Q := (a.1 * b.1, a.2 * b.2)")
    lines.append("def qadd (a b : Q) : Q := (a.1 * b.2 + b.1 * a.2, a.2 * b.2)")
    lines.append("def qneg (a : Q) : Q := (-a.1, a.2)")
    lines.append("def qge0 (a : Q) : Bool := (a.1 ≥ 0) == (a.2 > 0)")
    lines.append("def qlt0 (a : Q) : Bool := (a.1 < 0) == (a.2 > 0)")
    lines.append("")
    lines.append("def dot (u v : List Q) : Q :=")
    lines.append("  (u.zip v).foldl (fun acc p => qadd acc (qmul p.1 p.2)) (0, 1)")
    lines.append("")
    lines.append("def matColDot (A : List (List Q)) (y : List Q) (j : Nat) : Q :=")
    lines.append("  (A.zip y).foldl (fun acc p => qadd acc (qmul (p.1.getD j (0,1)) p.2)) (0, 1)")
    lines.append("")
    lines.append("def checkCert (A : List (List Q)) (b y : List Q) : Bool :=")
    lines.append("  let n := (A.head?.map List.length).getD 0")
    lines.append("  let yTA_ge0 := (List.range n).all (fun j => qge0 (matColDot A y j))")
    lines.append("  let yTb_lt0 := qlt0 (dot y b)")
    lines.append("  yTA_ge0 && yTb_lt0")
    lines.append("")
    
    # Generate certificates for all 84 × 64 = 5376 cases
    print("Generating certificates for κ ≤ 5 (5376 cases)...", file=sys.stderr)
    
    cert_data = []
    failed = 0
    
    for subset in combinations(range(9), 6):
        for vals in cart_product([-1, +1], repeat=6):
            A, b_vec = add_deterministic_constraints(A_base, b_base, list(subset), list(vals))
            y_float = find_farkas_certificate(A, b_vec)
            
            if y_float is None:
                print(f"FAIL: No certificate for {subset}, {vals}", file=sys.stderr)
                failed += 1
                continue
            
            y_rat = rationalize(y_float, A, b_vec)
            if y_rat is None:
                print(f"FAIL: Rationalization failed for {subset}, {vals}", file=sys.stderr)
                failed += 1
                continue
            
            cert_data.append((list(subset), list(vals), A, b_vec, y_rat))
    
    if failed > 0:
        print(f"ERROR: {failed} cases failed", file=sys.stderr)
        return None
    
    print(f"Generated {len(cert_data)} certificates", file=sys.stderr)
    
    # Emit certificates as Lean data
    lines.append("-- All 5376 certificates")
    lines.append("def certs : List (List (List Q) × List Q × List Q) := [")
    
    for i, (subset, vals, A, b_vec, y) in enumerate(cert_data):
        A_str = "[" + ", ".join("[" + ", ".join(f"({frac_to_lean(x)}, 1)" if isinstance(x, int) else f"({x.numerator}, {x.denominator})" for x in row) + "]" for row in A) + "]"
        b_str = "[" + ", ".join(f"({x.numerator}, {x.denominator})" for x in b_vec) + "]"
        y_str = "[" + ", ".join(f"({x.numerator}, {x.denominator})" for x in y) + "]"
        comma = "," if i < len(cert_data) - 1 else ""
        lines.append(f"  ({A_str}, {b_str}, {y_str}){comma}")
    
    lines.append("]")
    lines.append("")
    lines.append("def allCertsValid : Bool := certs.all (fun c => checkCert c.1 c.2.1 c.2.2)")
    lines.append("")
    lines.append("-- κ ≤ 5: all size-6 cases are infeasible")
    lines.append("theorem kappa_le_five : allCertsValid = true := by native_decide")
    lines.append("")
    
    # κ ≥ 5: exhibit one feasible size-5 assignment
    # Find a feasible one
    print("Finding feasible size-5 witness for κ ≥ 5...", file=sys.stderr)
    
    feasible_witness = None
    for subset in combinations(range(9), 5):
        for vals in cart_product([-1, +1], repeat=5):
            A, b_vec = add_deterministic_constraints(A_base, b_base, list(subset), list(vals))
            A_np = np.array([[float(x) for x in row] for row in A])
            b_np = np.array([float(x) for x in b_vec])
            
            # Check feasibility by trying to find x ≥ 0 with Ax = b
            m, n = A_np.shape
            res = linprog(np.zeros(n), A_eq=A_np, b_eq=b_np, bounds=(0, None), method='highs')
            
            if res.success:
                # Found feasible! Rationalize the solution
                x = res.x
                x_rat = [Fraction(xi).limit_denominator(1000) for xi in x]
                
                # Verify
                for i in range(m):
                    lhs = sum(A[i][j] * x_rat[j] for j in range(n))
                    if lhs != b_vec[i]:
                        # Adjust - find exact solution
                        break
                else:
                    feasible_witness = (list(subset), list(vals), A, b_vec, x_rat)
                    break
        if feasible_witness:
            break
    
    if feasible_witness:
        subset, vals, A, b_vec, x = feasible_witness
        print(f"Feasible witness: subset={subset}, vals={vals}", file=sys.stderr)
        
        lines.append("-- κ ≥ 5: one size-5 case is feasible")
        lines.append(f"-- Witness: observables {subset} with values {vals}")
        A_str = "[" + ", ".join("[" + ", ".join(f"({x.numerator}, {x.denominator})" for x in row) + "]" for row in A) + "]"
        b_str = "[" + ", ".join(f"({x.numerator}, {x.denominator})" for x in b_vec) + "]"
        x_str = "[" + ", ".join(f"({xi.numerator}, {xi.denominator})" for xi in x) + "]"
        
        lines.append(f"def A5 : List (List Q) := {A_str}")
        lines.append(f"def b5 : List Q := {b_str}")
        lines.append(f"def x5 : List Q := {x_str}")
        lines.append("")
        lines.append("def checkFeasible (A : List (List Q)) (b x : List Q) : Bool :=")
        lines.append("  (A.zip b).all (fun p => dot p.1 x == (p.2.1, p.2.2))")
        lines.append("  && x.all qge0")
        lines.append("")
        lines.append("theorem kappa_ge_five : checkFeasible A5 b5 x5 = true := by native_decide")
        lines.append("")
        lines.append("-- Combined: κ = 5")
        lines.append("theorem kappa_eq_five : allCertsValid ∧ checkFeasible A5 b5 x5 := ⟨kappa_le_five, kappa_ge_five⟩")
    else:
        lines.append("-- κ ≥ 5 witness: TBD (need exact rational solution)")
    
    return "\n".join(lines)


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--test':
        # Quick test
        A_base, b_base = build_base_constraints()
        print(f"Base system: {len(A_base)} constraints, {N_VARS} variables")
        
        # Test one case
        A, b = add_deterministic_constraints(A_base, b_base, [0,1,2,3,4,5], [1,1,1,1,1,1])
        y = find_farkas_certificate(A, b)
        if y is not None:
            y_rat = rationalize(y, A, b)
            print(f"Certificate found and rationalized: {y_rat is not None}")
        else:
            print("No certificate (feasible?)")
    else:
        code = generate_lean_file()
        if code:
            print(code)
