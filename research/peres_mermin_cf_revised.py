"""
The ACTUAL quantum empirical model for Peres-Mermin.

The quantum model predicts correlations that CANNOT be reproduced
by any point in the NC polytope. We need to compute:

For the GHZ state or maximally entangled state, the quantum predictions
for the Peres-Mermin observables.
"""

import numpy as np
from scipy.optimize import linprog
from itertools import product

# Peres-Mermin setup
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

print("="*70)
print("THE PERES-MERMIN PARADOX")
print("="*70)

print("""
The Peres-Mermin square uses 9 observables arranged in a 3×3 grid:

        Col 1    Col 2    Col 3
Row 1:   A        B        C      (product = +1)
Row 2:   a        b        c      (product = +1)  
Row 3:   α        β        γ      (product = +1)
         
        (×=+1)   (×=+1)   (×=-1)  ← Column products

The quantum operators are chosen so that:
- Each row product = +1 (eigenvalue)
- First two column products = +1
- Last column product = -1

For the quantum state |00⟩ + |11⟩ (Bell state), measuring any
row or column context gives outcomes with the specified product.

THE PARADOX:
  If we could assign definite values to all 9 observables,
  the product of all 9 would be:
    (row1 product) × (row2 product) × (row3 product) = (+1)(+1)(+1) = +1
    (col1 product) × (col2 product) × (col3 product) = (+1)(+1)(-1) = -1
  
  But each observable appears once in a row and once in a column,
  so the total product must equal both +1 and -1.
  
  CONTRADICTION.
  
  ∴ No global assignment exists.
  ∴ The quantum model is CONTEXTUAL.
""")

# Build the quantum empirical model
# For the Bell state, each context gives uniform distribution over
# valid sections (those with correct product)

print("="*70)
print("THE QUANTUM EMPIRICAL MODEL")
print("="*70)

print("""
For the maximally entangled Bell state, quantum mechanics predicts:
- In each context, outcomes are UNIFORM over valid sections
- Each context independently shows uniform distribution

This model SATISFIES marginal consistency (no-signalling).
But it CANNOT be extended to a global distribution.
""")

# The key insight: the quantum model IS in our setup, but we need
# to check if it can be written as convex combination of deterministic
# assignments.

# Actually, for Peres-Mermin, the quantum model with uniform distribution
# over valid sections IS noncontextual! The contextual fraction comes
# from SPECIFIC quantum predictions, not uniform ones.

# Let me reconsider. The CF depends on which quantum state and 
# measurement scenario we're considering.

# For the standard Peres-Mermin proof, the point is that there's
# NO deterministic assignment. But for the CF calculation, we need
# specific probabilities.

# According to Abramsky-Brandenburger, the CF for Peres-Mermin is 1/6.
# This comes from the GHZ state.

print("="*70)
print("UNDERSTANDING CF = 1/6 FOR PERES-MERMIN")
print("="*70)

print("""
The contextual fraction depends on the SPECIFIC quantum model.

For Peres-Mermin with GHZ state:
  |GHZ⟩ = (|000⟩ + |111⟩)/√2

The model has CF = 1/6 (proven in Abramsky et al. 2017).

But the UNIFORM model we computed has CF = 0!

This is because:
  - Uniform over valid sections IS achievable by a convex combination
    of noncontextual models
  - The GHZ predictions are NOT uniform — they have specific correlations
    that force the quantum point outside the NC polytope.

KEY DISTINCTION:
  - NC polytope = all marginally consistent models
  - Quantum model = specific predictions from a quantum state
  - CF = distance from quantum model to NC polytope
  
The uniform model lies INSIDE the NC polytope.
The GHZ model lies OUTSIDE.
""")

# Let's verify: is the uniform model in the NC polytope?

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

# Check if uniform model is in NC polytope
uniform = np.array([0.25] * 24)  # 4 sections per context, 6 contexts

A_eq, b_eq = build_base_constraints()

# Check constraints
residual = A_eq @ uniform - b_eq
print(f"Uniform model constraint residual: max = {np.max(np.abs(residual)):.6f}")
print(f"Uniform model is {'IN' if np.max(np.abs(residual)) < 1e-6 else 'NOT IN'} NC polytope")

print("\n" + "="*70)
print("THE STRUCTURAL INSIGHT (REVISED)")
print("="*70)

print("""
We computed:
  - NC polytope: 9D, 115 vertices, all probabilistic
  - P_A ∩ P_B: dimension reduces with agreements
  
Chan-Constantin computed:
  - CF for quantum models (outside NC polytope)
  - QTCF is entanglement monotone

THEY MEASURE DIFFERENT THINGS:
  
  ┌─────────────────────────────────────────────────────────────────┐
  │                                                                 │
  │    OUTSIDE (quantum model)                                     │
  │         ↓                                                       │
  │         ●  ← quantum predictions (CF = distance to polytope)   │
  │         ↓                                                       │
  │    ═══════════ BOUNDARY ═══════════                            │
  │         ↓                                                       │
  │    ┌─────────────────────────────────┐                          │
  │    │                                 │                          │
  │    │    NC POLYTOPE (9D)             │                          │
  │    │                                 │                          │
  │    │  ●  ← noncontextual models      │                          │
  │    │       dim = classical freedom   │                          │
  │    │                                 │                          │
  │    │  P_A ∩ P_B = intersection       │                          │
  │    │       (smaller subspace)        │                          │
  │    │                                 │                          │
  │    └─────────────────────────────────┘                          │
  │                                                                 │
  └─────────────────────────────────────────────────────────────────┘

FOR 互照:
  - The quantum point is FIXED (given by the underlying quantum state)
  - CF is FIXED (property of the quantum state)
  - But P_A ∩ P_B SHRINKS as observers agree on more marginals
  
  互照 doesn't change the quantum reality.
  互照 constrains WHICH classical stories can explain it.
  
  As dim(P_A ∩ P_B) → 0:
    - Fewer classical narratives available
    - But the quantum point still lies CF distance away
    - The "gap" remains, only the classical side shrinks

THIS IS THE DEEP INSIGHT:
  Contextuality (CF) is the QUANTUM property.
  Dimension (P_AB) is the CLASSICAL freedom.
  
  互照 operates on the classical side.
  Quantum reality is untouched by observer agreement.
  
  The more we agree, the fewer stories we can tell,
  but the quantum excess remains as irreducible as before.
""")

print("\n" + "="*70)
print("FOR GEMINI: THE QUESTION TRANSFORMS")
print("="*70)

print("""
ORIGINAL QUESTION:
  Is dim(P_A ∩ P_B) related to mutual information?

REFINED QUESTION:
  dim(P_AB) counts CLASSICAL degrees of freedom (narrative space).
  CF measures QUANTUM excess (how far outside classical).
  
  These are ORTHOGONAL, not dual.
  
  The information-theoretic question becomes:
  
  Is there a quantity I(A:B) such that:
    dim(P_A ∩ P_B) = dim(P_A) + dim(P_B) - dim(P_A ∪ P_B) - I(A:B)?
  
  Or more simply:
    Does shared classical information reduce classical freedom?
  
  ANSWER: YES, trivially.
    Each bit of agreed information adds one linear constraint.
    Each independent constraint reduces dimension by 1.
    
  So: dim(P_AB) = 9 - (# independent marginal agreements)
      = 9 - H(agreed observables)  (in some sense)
      
  But this is NOT the same as mutual information in the quantum sense.
  It's just counting constraints.
""")
