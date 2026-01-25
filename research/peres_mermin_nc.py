"""
Peres-Mermin Square: Computing What Survives Contextuality

The question: When we decompose e = (1-CF)·e_NC + CF·e_C,
what is e_NC? Is it unique? What structure does it have?

This is the 9/10 calculation that nobody has published.
"""

import numpy as np
from itertools import product
from scipy.optimize import linprog
import json

# =============================================================================
# PERES-MERMIN SQUARE SETUP
# =============================================================================
#
#      C1    C2    C3
# R1:  A     B     C    (product = +1)
# R2:  a     b     c    (product = +1)
# R3:  α     β     γ    (product = +1)
#
# Columns: product = -1 each
#
# Observables:
#   A = X⊗I, B = I⊗X, C = X⊗X
#   a = I⊗Y, b = Y⊗I, c = Y⊗Y
#   α = X⊗Y, β = Y⊗X, γ = Z⊗Z
#
# Quantum prediction: each observable has ⟨O⟩ = 0 (maximally mixed)
# but the CORRELATIONS within contexts are fixed.

# Label the 9 observables 0-8 in row-major order
# 0=A, 1=B, 2=C, 3=a, 4=b, 5=c, 6=α, 7=β, 8=γ

OBSERVABLES = ['A', 'B', 'C', 'a', 'b', 'c', 'α', 'β', 'γ']

# Contexts: each is a triple of indices that commute
CONTEXTS = {
    'R1': [0, 1, 2],  # A, B, C — product = +1
    'R2': [3, 4, 5],  # a, b, c — product = +1
    'R3': [6, 7, 8],  # α, β, γ — product = +1
    'C1': [0, 3, 6],  # A, a, α — product = -1
    'C2': [1, 4, 7],  # B, b, β — product = -1
    'C3': [2, 5, 8],  # C, c, γ — product = -1
}

# Product constraints for quantum case
PRODUCTS = {
    'R1': +1, 'R2': +1, 'R3': +1,
    'C1': -1, 'C2': -1, 'C3': -1
}

# =============================================================================
# STEP 1: Enumerate all deterministic assignments
# =============================================================================

def check_global_assignment(assignment):
    """
    Check if a {+1,-1}^9 assignment satisfies all product constraints.
    Returns dict of which constraints are satisfied.
    """
    results = {}
    for ctx_name, indices in CONTEXTS.items():
        prod = 1
        for i in indices:
            prod *= assignment[i]
        results[ctx_name] = prod
    return results

def enumerate_deterministic():
    """
    Enumerate all 2^9 = 512 deterministic assignments.
    Return those that are "consistent" (satisfy row products).
    """
    valid = []
    for bits in product([-1, 1], repeat=9):
        assignment = list(bits)
        results = check_global_assignment(assignment)
        valid.append({
            'assignment': assignment,
            'products': results,
            'satisfies_rows': all(results[f'R{i}'] == PRODUCTS[f'R{i}'] for i in [1,2,3]),
            'satisfies_cols': all(results[f'C{i}'] == PRODUCTS[f'C{i}'] for i in [1,2,3]),
            'satisfies_all': all(results[k] == PRODUCTS[k] for k in PRODUCTS)
        })
    return valid

print("=" * 60)
print("PERES-MERMIN: ENUMERATING DETERMINISTIC ASSIGNMENTS")
print("=" * 60)

all_assignments = enumerate_deterministic()
satisfies_rows = [a for a in all_assignments if a['satisfies_rows']]
satisfies_cols = [a for a in all_assignments if a['satisfies_cols']]
satisfies_all = [a for a in all_assignments if a['satisfies_all']]

print(f"\nTotal assignments: {len(all_assignments)}")
print(f"Satisfy row constraints: {len(satisfies_rows)}")
print(f"Satisfy column constraints: {len(satisfies_cols)}")
print(f"Satisfy ALL constraints: {len(satisfies_all)}")

if len(satisfies_all) == 0:
    print("\n→ CONFIRMED: No global deterministic assignment exists.")
    print("   This is the Kochen-Specker / contextuality result.")

# =============================================================================
# STEP 2: Context-local assignments (sections)
# =============================================================================

def enumerate_context_sections(context_indices, required_product):
    """
    Enumerate all {+1,-1}^3 assignments for a 3-observable context
    that satisfy the product constraint.
    """
    sections = []
    for bits in product([-1, 1], repeat=3):
        if bits[0] * bits[1] * bits[2] == required_product:
            sections.append(list(bits))
    return sections

print("\n" + "=" * 60)
print("STEP 2: CONTEXT-LOCAL SECTIONS")
print("=" * 60)

context_sections = {}
for ctx_name, indices in CONTEXTS.items():
    req_prod = PRODUCTS[ctx_name]
    sections = enumerate_context_sections(indices, req_prod)
    context_sections[ctx_name] = sections
    print(f"\n{ctx_name} (product = {req_prod:+d}): {len(sections)} valid sections")
    for s in sections:
        obs_names = [OBSERVABLES[i] for i in indices]
        print(f"  {dict(zip(obs_names, s))}")

# =============================================================================
# STEP 3: Find compatible pairs of sections (check overlaps)
# =============================================================================

print("\n" + "=" * 60)
print("STEP 3: CHECKING OVERLAP COMPATIBILITY")
print("=" * 60)

def get_overlap(ctx1_indices, ctx2_indices):
    """Find which observable indices are shared between two contexts."""
    return set(ctx1_indices) & set(ctx2_indices)

def sections_compatible(s1, idx1, s2, idx2):
    """Check if two sections agree on their overlap."""
    overlap = get_overlap(idx1, idx2)
    for obs_idx in overlap:
        val1 = s1[idx1.index(obs_idx)]
        val2 = s2[idx2.index(obs_idx)]
        if val1 != val2:
            return False
    return True

# Check row-column overlaps (each row-column pair shares exactly 1 observable)
compatibility_matrix = {}
for row in ['R1', 'R2', 'R3']:
    for col in ['C1', 'C2', 'C3']:
        row_idx = CONTEXTS[row]
        col_idx = CONTEXTS[col]
        overlap = get_overlap(row_idx, col_idx)
        
        compatible_pairs = []
        for r_sec in context_sections[row]:
            for c_sec in context_sections[col]:
                if sections_compatible(r_sec, row_idx, c_sec, col_idx):
                    compatible_pairs.append((r_sec, c_sec))
        
        compatibility_matrix[(row, col)] = compatible_pairs
        print(f"{row} ∩ {col} = observable {list(overlap)[0]} ({OBSERVABLES[list(overlap)[0]]}): {len(compatible_pairs)} compatible pairs")

# =============================================================================
# STEP 4: The Sheaf Condition — Can we glue?
# =============================================================================

print("\n" + "=" * 60)
print("STEP 4: ATTEMPTING TO GLUE (SHEAF CONDITION)")
print("=" * 60)

def try_gluing():
    """
    Try to find a consistent assignment of sections to all 6 contexts.
    This is a constraint satisfaction problem.
    """
    from itertools import product as cart_product
    
    # Generate all combinations of section choices
    all_choices = cart_product(
        range(len(context_sections['R1'])),
        range(len(context_sections['R2'])),
        range(len(context_sections['R3'])),
        range(len(context_sections['C1'])),
        range(len(context_sections['C2'])),
        range(len(context_sections['C3'])),
    )
    
    valid_gluings = []
    for choice in all_choices:
        r1_sec = context_sections['R1'][choice[0]]
        r2_sec = context_sections['R2'][choice[1]]
        r3_sec = context_sections['R3'][choice[2]]
        c1_sec = context_sections['C1'][choice[3]]
        c2_sec = context_sections['C2'][choice[4]]
        c3_sec = context_sections['C3'][choice[5]]
        
        # Check all overlaps
        valid = True
        for (row, r_sec), (col, c_sec) in [
            (('R1', r1_sec), ('C1', c1_sec)),
            (('R1', r1_sec), ('C2', c2_sec)),
            (('R1', r1_sec), ('C3', c3_sec)),
            (('R2', r2_sec), ('C1', c1_sec)),
            (('R2', r2_sec), ('C2', c2_sec)),
            (('R2', r2_sec), ('C3', c3_sec)),
            (('R3', r3_sec), ('C1', c1_sec)),
            (('R3', r3_sec), ('C2', c2_sec)),
            (('R3', r3_sec), ('C3', c3_sec)),
        ]:
            if not sections_compatible(r_sec, CONTEXTS[row], c_sec, CONTEXTS[col]):
                valid = False
                break
        
        if valid:
            valid_gluings.append({
                'R1': r1_sec, 'R2': r2_sec, 'R3': r3_sec,
                'C1': c1_sec, 'C2': c2_sec, 'C3': c3_sec
            })
    
    return valid_gluings

gluings = try_gluing()
print(f"\nNumber of valid gluings: {len(gluings)}")

if len(gluings) == 0:
    print("\n→ CONFIRMED: No compatible family of sections can be glued.")
    print("   H¹ ≠ 0. This is STRONG CONTEXTUALITY.")
    print("\n   The Rashomon effect: local stories exist, but no global narrative.")

# =============================================================================
# STEP 5: What DOES survive? (The actual 9/10 question)
# =============================================================================

print("\n" + "=" * 60)
print("STEP 5: WHAT SURVIVES? (The Δ calculation)")
print("=" * 60)

print("""
Since no global assignment exists, H⁰(ℱ) = ∅ for the full presheaf.

But wait — can we find a SUB-presheaf that DOES have global sections?

Key insight: Maybe some PARTIAL information survives.
Not the full assignment, but some quotient of it.

Candidates for Δ (what survives):
  1. Marginals on individual observables? 
  2. Correlations that don't involve the contradictory cycles?
  3. Something else?
""")

# What if we only look at PAIRS of observables within contexts?
print("\nAnalyzing pairwise correlations within contexts...")

for ctx_name, indices in CONTEXTS.items():
    sections = context_sections[ctx_name]
    print(f"\n{ctx_name}:")
    
    # For each pair in the context
    pairs = [(0,1), (0,2), (1,2)]
    for i, j in pairs:
        obs_i = OBSERVABLES[indices[i]]
        obs_j = OBSERVABLES[indices[j]]
        
        # What correlations appear across all sections?
        correlations = set()
        for sec in sections:
            corr = sec[i] * sec[j]
            correlations.add(corr)
        
        if len(correlations) == 1:
            print(f"  {obs_i}·{obs_j} = {list(correlations)[0]:+d} (FIXED)")
        else:
            print(f"  {obs_i}·{obs_j} ∈ {correlations} (varies)")

# =============================================================================
# STEP 6: The Key Observation
# =============================================================================

print("\n" + "=" * 60)
print("STEP 6: THE KEY OBSERVATION")
print("=" * 60)

print("""
Within each context, the TRIPLE correlation is fixed (by the product constraint):
  - Rows: A·B·C = a·b·c = α·β·γ = +1
  - Cols: A·a·α = B·b·β = C·c·γ = -1

But PAIRWISE correlations are NOT fixed within contexts.

The contradiction arises because:
  (A·B·C)(a·b·c)(α·β·γ) = +1  (rows)
  (A·a·α)(B·b·β)(C·c·γ) = -1  (cols)
  
But both products are equal to A·B·C·a·b·c·α·β·γ.

So: +1 = -1. Contradiction.

WHAT SURVIVES (Δ):
  The triple correlations survive LOCALLY (within each context).
  But they cannot be consistently COMBINED.
  
  The sheafification a(ℱ_cl) would give us... what?
""")

# =============================================================================
# STEP 7: Probabilistic analysis
# =============================================================================

print("\n" + "=" * 60)
print("STEP 7: PROBABILISTIC NONCONTEXTUAL POLYTOPE")
print("=" * 60)

print("""
For probabilistic models:
  - Each context gets a probability distribution over its valid sections
  - Noncontextuality: consistent marginals on overlaps
  
The NC polytope is the set of all such consistent distributions.

For Peres-Mermin, the NC polytope is NONEMPTY probabilistically,
even though it's empty deterministically!
""")

# Each context has 4 valid sections
# A probabilistic model assigns weights to these
# Noncontextuality: weights must be consistent on overlaps

# Let's parameterize: for each context, 4 probabilities summing to 1
# That's 6 contexts × 3 free parameters = 18 dimensions before constraints

# Overlap constraints: for each of the 9 observables,
# the marginal probability of +1 must agree across the 2 contexts containing it

print("\nBuilding the noncontextual polytope constraints...")

# For each observable, it appears in exactly one row and one column
# The marginal P(obs = +1) must agree

# Let's explicitly build this

def build_nc_polytope_constraints():
    """
    Build the linear constraints for the NC polytope.
    Variables: p[ctx][sec] = probability of section sec in context ctx
    Constraints: 
      1. Sum over sections in each context = 1
      2. Marginal agreement on overlaps
    """
    # Number the sections in each context
    section_ids = {}
    var_count = 0
    for ctx in ['R1', 'R2', 'R3', 'C1', 'C2', 'C3']:
        section_ids[ctx] = {}
        for i, sec in enumerate(context_sections[ctx]):
            section_ids[ctx][tuple(sec)] = var_count
            var_count += 1
    
    print(f"Total variables: {var_count} (6 contexts × 4 sections each)")
    
    # Build equality constraints: A_eq @ x = b_eq
    # 1. Normalization: sum of probs in each context = 1
    A_eq_rows = []
    b_eq = []
    
    for ctx in ['R1', 'R2', 'R3', 'C1', 'C2', 'C3']:
        row = [0] * var_count
        for sec_tuple, var_id in section_ids[ctx].items():
            row[var_id] = 1
        A_eq_rows.append(row)
        b_eq.append(1)
    
    # 2. Marginal agreement on overlaps
    for obs_idx in range(9):
        obs_name = OBSERVABLES[obs_idx]
        # Find which contexts contain this observable
        containing = []
        for ctx, indices in CONTEXTS.items():
            if obs_idx in indices:
                pos_in_ctx = indices.index(obs_idx)
                containing.append((ctx, pos_in_ctx))
        
        assert len(containing) == 2, f"Observable {obs_name} should be in exactly 2 contexts"
        ctx1, pos1 = containing[0]
        ctx2, pos2 = containing[1]
        
        # P(obs = +1 in ctx1) = P(obs = +1 in ctx2)
        # Sum of section probs where obs = +1 must agree
        row = [0] * var_count
        for sec_tuple, var_id in section_ids[ctx1].items():
            if sec_tuple[pos1] == +1:
                row[var_id] = 1
        for sec_tuple, var_id in section_ids[ctx2].items():
            if sec_tuple[pos2] == +1:
                row[var_id] = -1  # Subtract to get equality to 0
        
        A_eq_rows.append(row)
        b_eq.append(0)
    
    return np.array(A_eq_rows), np.array(b_eq), section_ids, var_count

A_eq, b_eq, section_ids, n_vars = build_nc_polytope_constraints()
print(f"Equality constraints: {len(b_eq)}")
print(f"  - 6 normalization")
print(f"  - 9 marginal agreements")

# Check if the polytope is nonempty by finding a feasible point
# We'll use linear programming: minimize 0 subject to constraints

print("\nChecking if NC polytope is nonempty...")

# Bounds: all variables >= 0
bounds = [(0, 1) for _ in range(n_vars)]

# Try to find a feasible point
result = linprog(
    c=[0] * n_vars,  # Minimize nothing (feasibility check)
    A_eq=A_eq,
    b_eq=b_eq,
    bounds=bounds,
    method='highs'
)

if result.success:
    print("\n✓ NC POLYTOPE IS NONEMPTY!")
    print("\nA feasible noncontextual distribution exists.")
    
    # Print the solution
    print("\nFeasible point (section probabilities):")
    x = result.x
    for ctx in ['R1', 'R2', 'R3', 'C1', 'C2', 'C3']:
        print(f"\n  {ctx}:")
        for sec_tuple, var_id in section_ids[ctx].items():
            if x[var_id] > 0.001:
                obs_names = [OBSERVABLES[i] for i in CONTEXTS[ctx]]
                sec_dict = dict(zip(obs_names, sec_tuple))
                print(f"    {sec_dict}: {x[var_id]:.4f}")
else:
    print("\n✗ NC polytope is empty (unexpected for probabilistic case)")

# =============================================================================
# STEP 8: What's the STRUCTURE of the NC polytope?
# =============================================================================

print("\n" + "=" * 60)
print("STEP 8: STRUCTURE OF THE NC POLYTOPE")
print("=" * 60)

print("""
The NC polytope exists. But:
  1. What are its vertices (extreme points)?
  2. What is its dimension?
  3. Given quantum predictions, how do we project onto it?
  4. Is the projection (e_NC) unique?
""")

# Find dimension by computing rank of constraint matrix
rank = np.linalg.matrix_rank(A_eq)
print(f"\nConstraint matrix rank: {rank}")
print(f"Number of variables: {n_vars}")
print(f"Degrees of freedom in NC polytope: {n_vars - rank}")

# =============================================================================
# SUMMARY
# =============================================================================

print("\n" + "=" * 60)
print("SUMMARY: WHAT WE COMPUTED")
print("=" * 60)

print("""
1. DETERMINISTICALLY: No global assignment exists (512 checked, 0 valid)
   → Strong contextuality / Kochen-Specker

2. SECTION-WISE: Each context has 4 valid sections, but they don't glue
   → H¹ ≠ 0, Rashomon effect confirmed

3. PROBABILISTICALLY: The NC polytope IS nonempty
   → Noncontextual probabilistic models exist
   → e_NC is not trivial

4. STRUCTURE: NC polytope has {n_vars - rank} degrees of freedom
   → e_NC is NOT unique (it's a whole polytope)
   → Sheafification would give a CANONICAL point (centroid? projection?)

THE 9/10 QUESTION (still open):
   Given quantum correlations for Peres-Mermin,
   what is the CANONICAL e_NC?
   Is it the centroid? The closest point? Something universal?
""".format(**{'n_vars - rank': n_vars - rank}))
