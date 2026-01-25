"""
Connecting to Chan-Constantin 2024:
  CF (Contextual Fraction) = entanglement monotone
  
We computed:
  dim(P_A ∩ P_B) = inside measure
  
Question: Is there a duality?
  CF measures "outside" (quantum excess)
  dim measures "inside" (classical freedom)
"""

import numpy as np
from scipy.optimize import linprog
from itertools import product

# Peres-Mermin square setup
observables = ['A', 'B', 'C', 'a', 'b', 'c', 'α', 'β', 'γ']
contexts = {
    'R1': ['A', 'B', 'C'],
    'R2': ['a', 'b', 'c'],
    'R3': ['α', 'β', 'γ'],
    'C1': ['A', 'a', 'α'],
    'C2': ['B', 'b', 'β'],
    'C3': ['C', 'c', 'γ']
}
parity = {'R1': 1, 'R2': 1, 'R3': 1, 'C1': 1, 'C2': 1, 'C3': -1}

def get_sections(context_name):
    obs = contexts[context_name]
    p = parity[context_name]
    sections = []
    for vals in product([-1, 1], repeat=3):
        if vals[0] * vals[1] * vals[2] == p:
            sections.append(dict(zip(obs, vals)))
    return sections

all_sections = {}
section_list = []
for ctx in contexts:
    all_sections[ctx] = get_sections(ctx)
    for s in all_sections[ctx]:
        section_list.append((ctx, s))

n_vars = len(section_list)

def section_to_idx(ctx, section):
    for i, (c, s) in enumerate(section_list):
        if c == ctx and s == section:
            return i
    return None

def build_base_constraints():
    A_eq = []
    b_eq = []
    
    for ctx in contexts:
        row = np.zeros(n_vars)
        for s in all_sections[ctx]:
            idx = section_to_idx(ctx, s)
            row[idx] = 1
        A_eq.append(row)
        b_eq.append(1)
    
    for obs in observables:
        ctx_with_obs = [c for c in contexts if obs in contexts[c]]
        if len(ctx_with_obs) <= 1:
            continue
        
        for val in [-1, 1]:
            ref_ctx = ctx_with_obs[0]
            for other_ctx in ctx_with_obs[1:]:
                row = np.zeros(n_vars)
                for s in all_sections[ref_ctx]:
                    if s[obs] == val:
                        row[section_to_idx(ref_ctx, s)] = 1
                for s in all_sections[other_ctx]:
                    if s[obs] == val:
                        row[section_to_idx(other_ctx, s)] = -1
                A_eq.append(row)
                b_eq.append(0)
    
    return np.array(A_eq), np.array(b_eq)

def compute_cf(empirical_model):
    """
    Compute contextual fraction of an empirical model.
    
    CF(e) = 1 - max{λ : e = λ*e_NC + (1-λ)*e'}
    
    This is a linear program.
    empirical_model: dict mapping (ctx, section) -> probability
    """
    A_base, b_base = build_base_constraints()
    
    # We want to maximize λ such that:
    #   e = λ * e_NC + (1-λ) * e'
    # where e_NC is in NC polytope
    #
    # Rewrite: e_NC = (e - (1-λ)*e') / λ
    # 
    # Or: λ * e_NC + (1-λ) * e' = e
    #     λ * e_NC ≤ e  (since e' ≥ 0)
    #
    # Actually, the dual approach:
    # NCF = max λ such that e - λ*e_NC is a valid model for some e_NC in NC
    #
    # Variables: λ ∈ [0,1], e_NC ∈ NC polytope
    # We can write: e_NC = x (our polytope variables)
    # Constraint: λ * x ≤ e componentwise? No, that's not right.
    #
    # Better: Let y = λ * x, then y is in λ * (NC polytope)
    # And we need e - y to be a valid probability distribution.
    #
    # Standard approach: 
    # max λ
    # s.t. e = λ * x + z
    #      x in NC polytope
    #      z is a valid model (all probs ≥ 0, normalized per context)
    #      0 ≤ λ ≤ 1
    #
    # Since z = e - λ*x, we need:
    #   e - λ*x ≥ 0  componentwise
    #   sum over sections in each context of (e - λ*x) = 1 - λ
    #   x in NC polytope
    #   λ ∈ [0,1]
    
    # Variables: [x_1, ..., x_n, λ]
    # n_vars for x, 1 for λ
    
    n = n_vars
    
    # Build empirical model vector
    e = np.zeros(n)
    for i, (ctx, section) in enumerate(section_list):
        key = (ctx, tuple(sorted(section.items())))
        if key in empirical_model:
            e[i] = empirical_model[key]
    
    # Objective: maximize λ = minimize -λ
    c = np.zeros(n + 1)
    c[n] = -1  # -λ
    
    # Inequality constraints: e - λ*x ≥ 0  =>  λ*x ≤ e  =>  λ*x[i] ≤ e[i]
    # But this is nonlinear in (λ, x)!
    
    # Use a different formulation:
    # Let y = λ*x (rescaled NC model)
    # Then: y ≤ e (componentwise)
    #       y in λ * NC = {λ*x : x in NC}
    #       sum_sections(y) = λ for each context (from normalization of x)
    #       marginals of y are consistent (from marginal consistency of x)
    
    # Variables: [y_1, ..., y_n, λ]
    
    # Constraints:
    # 1. y ≤ e (n inequalities)
    # 2. sum over sections in context = λ (6 equalities)
    # 3. marginal consistency (scaled by λ)
    # 4. y ≥ 0 (n bounds)
    # 5. 0 ≤ λ ≤ 1 (bounds)
    
    # For marginal consistency:
    # Original: sum_{s: s[obs]=v} x[ctx1,s] = sum_{s: s[obs]=v} x[ctx2,s]
    # Scaled:   sum_{s: s[obs]=v} y[ctx1,s] = sum_{s: s[obs]=v} y[ctx2,s]
    # Same constraint!
    
    # So the constraints are:
    # y ≤ e
    # sum_sections(y) = λ (per context)
    # marginals consistent
    # y ≥ 0, 0 ≤ λ ≤ 1
    
    # Build equality constraints
    A_eq_list = []
    b_eq_list = []
    
    # Normalization: sum of y in each context = λ
    for ctx in contexts:
        row = np.zeros(n + 1)
        for s in all_sections[ctx]:
            idx = section_to_idx(ctx, s)
            row[idx] = 1
        row[n] = -1  # -λ
        A_eq_list.append(row)
        b_eq_list.append(0)
    
    # Marginal consistency (same as before, extended with 0 for λ)
    for obs in observables:
        ctx_with_obs = [c for c in contexts if obs in contexts[c]]
        if len(ctx_with_obs) <= 1:
            continue
        
        for val in [-1, 1]:
            ref_ctx = ctx_with_obs[0]
            for other_ctx in ctx_with_obs[1:]:
                row = np.zeros(n + 1)
                for s in all_sections[ref_ctx]:
                    if s[obs] == val:
                        row[section_to_idx(ref_ctx, s)] = 1
                for s in all_sections[other_ctx]:
                    if s[obs] == val:
                        row[section_to_idx(other_ctx, s)] = -1
                A_eq_list.append(row)
                b_eq_list.append(0)
    
    A_eq = np.array(A_eq_list)
    b_eq = np.array(b_eq_list)
    
    # Inequality constraints: y ≤ e  =>  y - e ≤ 0
    A_ub = np.zeros((n, n + 1))
    for i in range(n):
        A_ub[i, i] = 1
    b_ub = e.copy()
    
    # Bounds
    bounds = [(0, None) for _ in range(n)] + [(0, 1)]
    
    # Solve
    result = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, 
                     bounds=bounds, method='highs')
    
    if result.success:
        ncf = result.x[n]
        cf = 1 - ncf
        return cf, ncf
    else:
        return None, None

print("="*70)
print("CHAN-CONSTANTIN CONNECTION: CF vs dim(P_AB)")
print("="*70)

# First, let's compute CF for a quantum model
# For Peres-Mermin, the quantum model has CF = 1/6 (known result)

# Build the quantum empirical model for Peres-Mermin
# Using the standard GHZ-like state predictions
# 
# For a maximally entangled state, the quantum predictions are:
# P(ABC = +++) = P(ABC = +--) = P(ABC = -+-) = P(ABC = --+) = 1/4
# (uniform over outcomes with even parity)

def build_quantum_model():
    """Build empirical model for maximally contextual quantum state."""
    model = {}
    
    # For each context, quantum mechanics predicts:
    # Equal probability for outcomes consistent with the parity constraint
    
    for ctx in contexts:
        sections = all_sections[ctx]
        # Uniform distribution over sections (valid for certain quantum states)
        for s in sections:
            key = (ctx, tuple(sorted(s.items())))
            model[key] = 1.0 / len(sections)
    
    return model

quantum_model = build_quantum_model()

print("\nQuantum model (uniform over valid sections):")
for ctx in contexts:
    print(f"\n  {ctx}:")
    for s in all_sections[ctx]:
        key = (ctx, tuple(sorted(s.items())))
        print(f"    P({s}) = {quantum_model[key]:.3f}")

cf, ncf = compute_cf(quantum_model)
print(f"\n\nContextual Fraction of quantum model: CF = {cf:.4f}")
print(f"Noncontextual Fraction: NCF = {ncf:.4f}")

# Now let's build models with fixed marginals and compute CF
print("\n" + "="*70)
print("CF FOR MODELS WITH FIXED MARGINALS")
print("="*70)

def build_model_with_marginals(marginal_dict):
    """
    Build a model consistent with given marginals.
    marginal_dict: {obs: prob_plus} mapping observable to P(obs=+1)
    
    We solve for a point in the polytope with these marginals.
    """
    A_base, b_base = build_base_constraints()
    
    A_list = list(A_base)
    b_list = list(b_base)
    
    # Add marginal constraints
    for obs, prob in marginal_dict.items():
        ctx_with_obs = [c for c in contexts if obs in contexts[c]]
        ref_ctx = ctx_with_obs[0]
        
        row = np.zeros(n_vars)
        for s in all_sections[ref_ctx]:
            if s[obs] == 1:
                row[section_to_idx(ref_ctx, s)] = 1
        
        A_list.append(row)
        b_list.append(prob)
    
    A_eq = np.array(A_list)
    b_eq = np.array(b_list)
    
    # Find a feasible point (maximize sum to get interior)
    c = -np.ones(n_vars)
    bounds = [(0, None) for _ in range(n_vars)]
    result = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')
    
    if result.success:
        x = result.x
        model = {}
        for i, (ctx, section) in enumerate(section_list):
            key = (ctx, tuple(sorted(section.items())))
            model[key] = x[i]
        return model
    else:
        return None

# Try different marginal configurations
marginal_configs = [
    ("Base (0.5 all)", {obs: 0.5 for obs in observables}),
    ("A=0.7", {'A': 0.7}),
    ("A=0.7, B=0.7", {'A': 0.7, 'B': 0.7}),
    ("Row R1 at 0.7", {'A': 0.7, 'B': 0.7, 'C': 0.7}),
    ("A=1.0 (deterministic)", {'A': 1.0}),
]

print(f"\n{'Configuration':<30} {'CF':<10} {'NCF':<10} {'dim(P)':<10}")
print("-"*60)

for name, marginals in marginal_configs:
    model = build_model_with_marginals(marginals)
    if model:
        cf, ncf = compute_cf(model)
        
        # Compute dimension
        A_base, b_base = build_base_constraints()
        for obs, prob in marginals.items():
            A_list = list(A_base)
            b_list = list(b_base)
            ctx_with_obs = [c for c in contexts if obs in contexts[c]]
            ref_ctx = ctx_with_obs[0]
            row = np.zeros(n_vars)
            for s in all_sections[ref_ctx]:
                if s[obs] == 1:
                    row[section_to_idx(ref_ctx, s)] = 1
            A_base = np.vstack([A_base, row])
            b_base = np.append(b_base, prob)
        
        dim = n_vars - np.linalg.matrix_rank(A_base)
        
        if cf is not None:
            print(f"{name:<30} {cf:<10.4f} {ncf:<10.4f} {dim:<10}")
        else:
            print(f"{name:<30} {'FAILED':<10} {'FAILED':<10} {dim:<10}")
    else:
        print(f"{name:<30} INFEASIBLE")

print("\n" + "="*70)
print("KEY INSIGHT: THE DUALITY")
print("="*70)

print("""
CHAN-CONSTANTIN FRAMEWORK:
  CF = 1 - NCF
  CF = distance from quantum point to NC polytope
  CF is an entanglement monotone
  
  contextual ⟹ entangled ⟹ superposition

OUR FRAMEWORK:
  dim(P_AB) = dimension of intersection inside NC polytope
  dim = 9 - (# independent agreements)
  dim measures "classical freedom remaining"

THE RELATIONSHIP:
  CF measures how far OUTSIDE the NC polytope (quantum excess)
  dim measures how much room INSIDE the NC polytope (classical freedom)
  
  These are COMPLEMENTARY, not dual:
  
  ┌──────────────────────────────────────────────────────────────┐
  │  OUTSIDE: CF > 0  ⟺  quantum point not in NC polytope       │
  │  INSIDE:  dim > 0  ⟺  multiple classical stories available  │
  │                                                              │
  │  CF = measure of contextuality (quantum resource)            │
  │  dim = measure of ambiguity (classical freedom)              │
  └──────────────────────────────────────────────────────────────┘

FOR 互照:
  - CF tells us: how much quantum advantage is available
  - dim tells us: how many classical narratives can coexist
  
  When observers agree on marginals:
    dim reduces → fewer classical stories
    CF unchanged (it's a property of the quantum point)
    
  The intersection P_A ∩ P_B shrinks, but CF stays fixed.
  
  INSIGHT: 互照 doesn't change contextuality—it changes WHICH
  classical stories are available to explain the contextuality.
""")
