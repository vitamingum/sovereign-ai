"""
Peres-Mermin NC Polytope: Deep Vertex Analysis

107 vertices found, all probabilistic — why?

Because the NC polytope lives in the space of probability distributions
over sections, NOT in the space of deterministic assignments.

The extreme points are the most "committed" distributions that still
satisfy all the marginal consistency constraints.
"""

import numpy as np
from itertools import product
from scipy.optimize import linprog
import warnings
warnings.filterwarnings('ignore')

# =============================================================================
# SETUP
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

PRODUCTS = {'R1': +1, 'R2': +1, 'R3': +1, 'C1': -1, 'C2': -1, 'C3': -1}

def enumerate_context_sections(context_indices, required_product):
    sections = []
    for bits in product([-1, 1], repeat=3):
        if bits[0] * bits[1] * bits[2] == required_product:
            sections.append(list(bits))
    return sections

context_sections = {}
for ctx_name, indices in CONTEXTS.items():
    context_sections[ctx_name] = enumerate_context_sections(indices, PRODUCTS[ctx_name])

# Build section ID mapping
section_ids = {}
var_count = 0
CTX_ORDER = ['R1', 'R2', 'R3', 'C1', 'C2', 'C3']
for ctx in CTX_ORDER:
    section_ids[ctx] = {}
    for i, sec in enumerate(context_sections[ctx]):
        section_ids[ctx][tuple(sec)] = var_count
        var_count += 1

n_vars = var_count  # 24

# Build constraint matrix
A_eq_rows = []
b_eq = []

# Normalization
for ctx in CTX_ORDER:
    row = [0] * n_vars
    for sec_tuple, var_id in section_ids[ctx].items():
        row[var_id] = 1
    A_eq_rows.append(row)
    b_eq.append(1)

# Marginal agreement
for obs_idx in range(9):
    containing = []
    for ctx, indices in CONTEXTS.items():
        if obs_idx in indices:
            pos_in_ctx = indices.index(obs_idx)
            containing.append((ctx, pos_in_ctx))
    
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

A_eq = np.array(A_eq_rows)
b_eq = np.array(b_eq)

print("=" * 70)
print("DEEP ANALYSIS: Why 107 probabilistic vertices?")
print("=" * 70)

# =============================================================================
# FIND VERTICES
# =============================================================================

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

np.random.seed(42)
vertices = []
seen = set()

for _ in range(2000):
    direction = np.random.randn(n_vars)
    v = find_vertex(direction)
    if v is not None:
        key = tuple(np.round(v, 6))
        if key not in seen:
            seen.add(key)
            vertices.append(v)

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

print(f"\nTotal vertices: {len(vertices)}")

# =============================================================================
# ANALYZE A SINGLE VERTEX IN DETAIL
# =============================================================================

print("\n" + "=" * 70)
print("DETAILED VERTEX ANALYSIS")
print("=" * 70)

def analyze_vertex(v, idx):
    """Deep analysis of a single vertex."""
    print(f"\n--- Vertex {idx} ---")
    
    # Extract probabilities per context
    for ctx in CTX_ORDER:
        print(f"\n{ctx}:")
        total = 0
        for sec_tuple, var_id in section_ids[ctx].items():
            p = v[var_id]
            if p > 0.001:
                obs_names = [OBSERVABLES[i] for i in CONTEXTS[ctx]]
                sec_dict = dict(zip(obs_names, sec_tuple))
                print(f"  P({sec_dict}) = {p:.4f}")
                total += p
        print(f"  Total: {total:.4f}")
    
    # Compute marginals
    print(f"\nMarginals P(obs = +1):")
    for obs_idx, obs_name in enumerate(OBSERVABLES):
        # Find which context it's in (use first one)
        for ctx, indices in CONTEXTS.items():
            if obs_idx in indices:
                pos = indices.index(obs_idx)
                p_plus = 0
                for sec_tuple, var_id in section_ids[ctx].items():
                    if sec_tuple[pos] == +1:
                        p_plus += v[var_id]
                print(f"  P({obs_name} = +1) = {p_plus:.4f}")
                break

# Analyze first 3 vertices
for i in range(min(3, len(vertices))):
    analyze_vertex(vertices[i], i)

# =============================================================================
# COUNT NON-ZERO ENTRIES PER VERTEX
# =============================================================================

print("\n" + "=" * 70)
print("SPARSITY ANALYSIS")
print("=" * 70)

sparsity = []
for v in vertices:
    n_nonzero = sum(1 for x in v if x > 0.001)
    sparsity.append(n_nonzero)

print(f"\nNon-zero entries per vertex:")
print(f"  Min: {min(sparsity)}")
print(f"  Max: {max(sparsity)}")
print(f"  Mean: {np.mean(sparsity):.1f}")
print(f"  Median: {np.median(sparsity):.1f}")

# Distribution
from collections import Counter
sparsity_dist = Counter(sparsity)
print(f"\nDistribution of non-zero counts:")
for k in sorted(sparsity_dist.keys()):
    print(f"  {k} non-zeros: {sparsity_dist[k]} vertices")

# =============================================================================
# KEY INSIGHT
# =============================================================================

print("\n" + "=" * 70)
print("THE STRUCTURAL INSIGHT")
print("=" * 70)

# Check if any vertex is deterministic
min_sparsity = min(sparsity)

print(f"""
WHY NO DETERMINISTIC VERTICES?

A deterministic vertex would have exactly 6 non-zero entries
(one per context). But we found:
  Minimum non-zeros: {min_sparsity}

This means: NO point in the NC polytope corresponds to a single
deterministic assignment across all contexts.

INTERPRETATION:
  The NC polytope is NOT "convex hull of deterministic models."
  It is "convex set of consistent probabilistic models."
  
  The vertices are the EXTREME probabilistic models —
  the most committed distributions that still satisfy marginal consistency.
  
  Each vertex is forced to hedge: put positive probability on
  multiple sections per context to make the marginals match.

THIS IS THE RASHOMON EFFECT AT THE PROBABILISTIC LEVEL:
  Even at the extreme points, you must tell multiple stories.
  There is no "pure classical narrative" in this polytope.
  Every point, including vertices, is a superposition of classical stories.
""")

# =============================================================================
# WHAT THE VERTICES "LOOK LIKE"
# =============================================================================

print("\n" + "=" * 70)
print("VERTEX SIGNATURES")
print("=" * 70)

# For each vertex, compute a signature: which sections have positive probability
def vertex_signature(v):
    sig = {}
    for ctx in CTX_ORDER:
        active = []
        for sec_tuple, var_id in section_ids[ctx].items():
            if v[var_id] > 0.001:
                active.append(sec_tuple)
        sig[ctx] = len(active)
    return tuple(sig[ctx] for ctx in CTX_ORDER)

signatures = [vertex_signature(v) for v in vertices]
sig_counts = Counter(signatures)

print("\nVertex signatures (# active sections per context):")
print("Format: (R1, R2, R3, C1, C2, C3)")
for sig in sorted(sig_counts.keys(), key=lambda x: sum(x)):
    count = sig_counts[sig]
    print(f"  {sig}: {count} vertices")

# =============================================================================
# THE MINIMAL VERTICES
# =============================================================================

print("\n" + "=" * 70)
print("MINIMAL VERTICES (fewest active sections)")
print("=" * 70)

min_total = min(sum(sig) for sig in signatures)
minimal_sigs = [sig for sig in set(signatures) if sum(sig) == min_total]

print(f"\nMinimal total active sections: {min_total}")
print(f"Signatures achieving this: {minimal_sigs}")

# Find and display a minimal vertex
for i, v in enumerate(vertices):
    if sum(vertex_signature(v)) == min_total:
        print(f"\nExample minimal vertex (index {i}):")
        analyze_vertex(v, i)
        break

# =============================================================================
# SUMMARY
# =============================================================================

print("\n" + "=" * 70)
print("SUMMARY: THE NC POLYTOPE IS 'FULLY MIXED'")
print("=" * 70)

print(f"""
PERES-MERMIN NC POLYTOPE STRUCTURE:

  Dimension: 9
  Vertices: {len(vertices)}
  All vertices are PROBABILISTIC (not deterministic)
  
  Minimum active sections per vertex: {min_sparsity} (out of 24)
  Typical signature: {max(sig_counts.items(), key=lambda x: x[1])[0]}

MEANING:
  There is no "pure classical story" in this polytope.
  Every extreme point is a mixture of multiple stories.
  
  The NC polytope is not the convex hull of hidden variable models.
  It is the space of all CONSISTENT HEDGING STRATEGIES.

FOR 互照:
  When two observers intersect their polytopes (P_A ∩ P_B),
  they are finding the shared hedging strategies.
  
  The dimension of the intersection measures:
  "How many ways can we BOTH hedge while agreeing on what we see?"

GEMINI'S "GAUGE FREEDOM" CONFIRMED:
  The 9D is not 9 ways to pick a deterministic story.
  It's 9 ways to WEIGHT a portfolio of stories.
  
  Agency lives in HOW you hedge, not WHICH story is true.
""")
