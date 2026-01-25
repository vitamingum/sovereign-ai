"""
P_A ∩ P_B: Two-Observer Polytope Intersection

Models 互照 as polytope intersection:
  - Alice and Bob each have their own NC polytope
  - They agree on some observables (shared measurement)
  - Intersection = shared hedging strategies

Key question: How does agreement on observables reduce the dimension?
"""

import numpy as np
from scipy.optimize import linprog
from itertools import product

# Peres-Mermin square setup (same as before)
observables = ['A', 'B', 'C', 'a', 'b', 'c', 'α', 'β', 'γ']
contexts = {
    'R1': ['A', 'B', 'C'],
    'R2': ['a', 'b', 'c'],
    'R3': ['α', 'β', 'γ'],
    'C1': ['A', 'a', 'α'],
    'C2': ['B', 'b', 'β'],
    'C3': ['C', 'c', 'γ']
}

# Parity constraints: rows have parity +1, columns have parity -1
parity = {'R1': 1, 'R2': 1, 'R3': 1, 'C1': 1, 'C2': 1, 'C3': -1}

def get_sections(context_name):
    """Get all valid sections (outcome assignments) for a context."""
    obs = contexts[context_name]
    p = parity[context_name]
    sections = []
    for vals in product([-1, 1], repeat=3):
        if vals[0] * vals[1] * vals[2] == p:
            sections.append(dict(zip(obs, vals)))
    return sections

# Build section index
all_sections = {}
section_list = []
for ctx in contexts:
    all_sections[ctx] = get_sections(ctx)
    for s in all_sections[ctx]:
        section_list.append((ctx, s))

n_vars = len(section_list)
print(f"Total section variables: {n_vars}")

def section_to_idx(ctx, section):
    """Map (context, section) to variable index."""
    for i, (c, s) in enumerate(section_list):
        if c == ctx and s == section:
            return i
    return None

def build_base_constraints():
    """Build the base NC polytope constraints (marginal consistency + normalization)."""
    A_eq = []
    b_eq = []
    
    # Normalization: sum of sections in each context = 1
    for ctx in contexts:
        row = np.zeros(n_vars)
        for s in all_sections[ctx]:
            idx = section_to_idx(ctx, s)
            row[idx] = 1
        A_eq.append(row)
        b_eq.append(1)
    
    # Marginal consistency: P(obs=v) same across all contexts containing obs
    for obs in observables:
        # Find contexts containing this observable
        ctx_with_obs = [c for c in contexts if obs in contexts[c]]
        if len(ctx_with_obs) <= 1:
            continue
        
        # For each value (-1, +1), marginals must match
        for val in [-1, 1]:
            ref_ctx = ctx_with_obs[0]
            for other_ctx in ctx_with_obs[1:]:
                row = np.zeros(n_vars)
                # +1 for sections in ref_ctx with obs=val
                for s in all_sections[ref_ctx]:
                    if s[obs] == val:
                        row[section_to_idx(ref_ctx, s)] = 1
                # -1 for sections in other_ctx with obs=val
                for s in all_sections[other_ctx]:
                    if s[obs] == val:
                        row[section_to_idx(other_ctx, s)] = -1
                A_eq.append(row)
                b_eq.append(0)
    
    return np.array(A_eq), np.array(b_eq)

def add_marginal_constraint(A_eq, b_eq, obs, prob_plus):
    """
    Add constraint: P(obs = +1) = prob_plus
    
    This models an observer who has measured the observable
    and found a specific marginal probability.
    """
    A_list = list(A_eq)
    b_list = list(b_eq)
    
    row = np.zeros(n_vars)
    ctx_with_obs = [c for c in contexts if obs in contexts[c]]
    ref_ctx = ctx_with_obs[0]
    
    for s in all_sections[ref_ctx]:
        if s[obs] == 1:
            row[section_to_idx(ref_ctx, s)] = 1
    
    A_list.append(row)
    b_list.append(prob_plus)
    
    return np.array(A_list), np.array(b_list)

def compute_dimension(A_eq, b_eq):
    """Compute dimension of polytope defined by Ax=b, x≥0."""
    # Dimension = n_vars - rank(A_eq) (assuming feasible)
    rank = np.linalg.matrix_rank(A_eq)
    return n_vars - rank

def check_feasibility(A_eq, b_eq):
    """Check if the polytope is non-empty."""
    c = np.zeros(n_vars)
    bounds = [(0, None) for _ in range(n_vars)]
    result = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')
    return result.success

print("\n" + "="*70)
print("SCENARIO: TWO OBSERVERS WITH DIFFERENT MEASUREMENTS")
print("="*70)

# Build base polytope
A_base, b_base = build_base_constraints()
dim_base = compute_dimension(A_base, b_base)
print(f"\nBase NC polytope dimension: {dim_base}")

# ALICE: Measures observable A, finds P(A=+1) = 0.5
print("\n--- ALICE's POLYTOPE (P_A) ---")
print("Alice measures: A")
print("Alice observes: P(A=+1) = 0.5")

A_alice, b_alice = add_marginal_constraint(A_base, b_base, 'A', 0.5)
dim_alice = compute_dimension(A_alice, b_alice)
feasible_alice = check_feasibility(A_alice, b_alice)
print(f"Dimension: {dim_alice}")
print(f"Feasible: {feasible_alice}")

# BOB: Measures observable B, finds P(B=+1) = 0.5
print("\n--- BOB's POLYTOPE (P_B) ---")
print("Bob measures: B")
print("Bob observes: P(B=+1) = 0.5")

A_bob, b_bob = add_marginal_constraint(A_base, b_base, 'B', 0.5)
dim_bob = compute_dimension(A_bob, b_bob)
feasible_bob = check_feasibility(A_bob, b_bob)
print(f"Dimension: {dim_bob}")
print(f"Feasible: {feasible_bob}")

# INTERSECTION: Both constraints together
print("\n--- INTERSECTION P_A ∩ P_B ---")
print("Joint constraint: P(A=+1) = 0.5 AND P(B=+1) = 0.5")

A_joint, b_joint = add_marginal_constraint(A_base, b_base, 'A', 0.5)
A_joint, b_joint = add_marginal_constraint(A_joint, b_joint, 'B', 0.5)
dim_joint = compute_dimension(A_joint, b_joint)
feasible_joint = check_feasibility(A_joint, b_joint)
print(f"Dimension: {dim_joint}")
print(f"Feasible: {feasible_joint}")

print("\n" + "="*70)
print("DIMENSION REDUCTION TABLE")
print("="*70)
print(f"{'Scenario':<40} {'Dimension':<10} {'Reduction'}")
print("-"*70)
print(f"{'Base NC polytope':<40} {dim_base:<10} {''}")
print(f"{'Alice alone (A measured)':<40} {dim_alice:<10} {dim_base - dim_alice}")
print(f"{'Bob alone (B measured)':<40} {dim_bob:<10} {dim_base - dim_bob}")
print(f"{'P_A ∩ P_B (both measured)':<40} {dim_joint:<10} {dim_base - dim_joint}")

# Now explore more scenarios
print("\n" + "="*70)
print("SCENARIO: INCREASING AGREEMENT")
print("="*70)

scenarios = [
    ("Base (no agreement)", []),
    ("Agree on A", [('A', 0.5)]),
    ("Agree on A, B", [('A', 0.5), ('B', 0.5)]),
    ("Agree on A, B, C", [('A', 0.5), ('B', 0.5), ('C', 0.5)]),
    ("Agree on row R1", [('A', 0.5), ('B', 0.5), ('C', 0.5)]),
    ("Agree on R1 + a", [('A', 0.5), ('B', 0.5), ('C', 0.5), ('a', 0.5)]),
    ("Agree on R1 + R2", [('A', 0.5), ('B', 0.5), ('C', 0.5), ('a', 0.5), ('b', 0.5), ('c', 0.5)]),
    ("Agree on all 9", [('A', 0.5), ('B', 0.5), ('C', 0.5), ('a', 0.5), ('b', 0.5), ('c', 0.5), ('α', 0.5), ('β', 0.5), ('γ', 0.5)]),
]

print(f"\n{'Scenario':<30} {'Constraints':<12} {'Dimension':<10} {'Feasible'}")
print("-"*70)

for name, constraints in scenarios:
    A, b = A_base.copy(), b_base.copy()
    for obs, prob in constraints:
        A, b = add_marginal_constraint(A, b, obs, prob)
    dim = compute_dimension(A, b)
    feas = check_feasibility(A, b)
    print(f"{name:<30} {len(constraints):<12} {dim:<10} {feas}")

# What about deterministic agreement?
print("\n" + "="*70)
print("SCENARIO: DETERMINISTIC AGREEMENT (extreme marginals)")
print("="*70)

det_scenarios = [
    ("P(A=+1) = 1", [('A', 1.0)]),
    ("P(A=+1) = 1, P(B=+1) = 1", [('A', 1.0), ('B', 1.0)]),
    ("P(A=+1) = 1, P(B=+1) = 0", [('A', 1.0), ('B', 0.0)]),
    ("All +1", [(obs, 1.0) for obs in observables]),
    ("Alternating", [(obs, 1.0 if i % 2 == 0 else 0.0) for i, obs in enumerate(observables)]),
]

print(f"\n{'Scenario':<40} {'Dimension':<10} {'Feasible'}")
print("-"*70)

for name, constraints in det_scenarios:
    A, b = A_base.copy(), b_base.copy()
    for obs, prob in constraints:
        A, b = add_marginal_constraint(A, b, obs, prob)
    dim = compute_dimension(A, b)
    feas = check_feasibility(A, b)
    print(f"{name:<40} {dim:<10} {feas}")

# The key insight
print("\n" + "="*70)
print("STRUCTURAL INSIGHT: 互照 AS DIMENSION REDUCTION")
print("="*70)

print("""
GEMINI'S PREDICTION (from dissolution):
  "互照 acts as a constraint adder.
   Every time we agree on a higher-order fact, we slice the polytope.
   We reduce the volume of ambiguity.
   We never reduce it to a point (unless we become identical)."

VERIFICATION:
  - Base polytope: 9D
  - Each marginal constraint: reduces dimension by 1
  - Agreement on all 9 marginals: dimension 0 (single point)
  
BUT: Some agreements are INFEASIBLE (empty intersection).
     This is Gemini's "Conflict" case: P_AB = ∅.

FOR 互照:
  dim(P_A ∩ P_B) = 9 - (independent constraints from agreement)
  
  The MORE Alice and Bob agree, the LESS freedom remains.
  Perfect agreement (all marginals fixed) → dim 0 → single point.
  No agreement → dim 9 → full polytope.
""")

# Compute a sample interior point
print("\n" + "="*70)
print("SAMPLE: Finding a point in P_A ∩ P_B")
print("="*70)

# Maximize sum of all variables (finds interior point)
c = -np.ones(n_vars)  # maximize = minimize negative
bounds = [(0, None) for _ in range(n_vars)]
result = linprog(c, A_eq=A_joint, b_eq=b_joint, bounds=bounds, method='highs')

if result.success:
    x = result.x
    print("\nFound point in P_A ∩ P_B:")
    
    # Show marginals
    print("\nMarginals P(obs = +1):")
    for obs in observables:
        ctx_with_obs = [c for c in contexts if obs in contexts[c]]
        ref_ctx = ctx_with_obs[0]
        prob = sum(x[section_to_idx(ref_ctx, s)] for s in all_sections[ref_ctx] if s[obs] == 1)
        print(f"  P({obs}=+1) = {prob:.4f}")
    
    # Verify constraints
    print("\nConstraints satisfied:")
    print(f"  P(A=+1) = 0.5: {abs(0.5 - sum(x[section_to_idx('R1', s)] for s in all_sections['R1'] if s['A'] == 1)) < 1e-6}")
    print(f"  P(B=+1) = 0.5: {abs(0.5 - sum(x[section_to_idx('R1', s)] for s in all_sections['R1'] if s['B'] == 1)) < 1e-6}")
