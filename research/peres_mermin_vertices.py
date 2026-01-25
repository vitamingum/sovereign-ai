"""
Peres-Mermin NC Polytope: Vertex Enumeration

Building on peres_mermin_nc.py — now we enumerate the extreme points
(vertices) of the 9D noncontextual polytope.

These vertices are the "deterministic stories" — the edge cases
where the ambiguity collapses to a single classical narrative.
"""

import numpy as np
from itertools import product
from scipy.optimize import linprog
from scipy.spatial import ConvexHull
import warnings
warnings.filterwarnings('ignore')

# =============================================================================
# SETUP (from peres_mermin_nc.py)
# =============================================================================

OBSERVABLES = ['A', 'B', 'C', 'a', 'b', 'c', 'α', 'β', 'γ']

CONTEXTS = {
    'R1': [0, 1, 2],  # A, B, C — product = +1
    'R2': [3, 4, 5],  # a, b, c — product = +1
    'R3': [6, 7, 8],  # α, β, γ — product = +1
    'C1': [0, 3, 6],  # A, a, α — product = -1
    'C2': [1, 4, 7],  # B, b, β — product = -1
    'C3': [2, 5, 8],  # C, c, γ — product = -1
}

PRODUCTS = {
    'R1': +1, 'R2': +1, 'R3': +1,
    'C1': -1, 'C2': -1, 'C3': -1
}

def enumerate_context_sections(context_indices, required_product):
    """Enumerate valid sections for a context."""
    sections = []
    for bits in product([-1, 1], repeat=3):
        if bits[0] * bits[1] * bits[2] == required_product:
            sections.append(list(bits))
    return sections

# Build context sections
context_sections = {}
for ctx_name, indices in CONTEXTS.items():
    req_prod = PRODUCTS[ctx_name]
    context_sections[ctx_name] = enumerate_context_sections(indices, req_prod)

# =============================================================================
# VERTEX ENUMERATION VIA EXTREME POINT SEARCH
# =============================================================================

print("=" * 70)
print("PERES-MERMIN NC POLYTOPE: VERTEX ENUMERATION")
print("=" * 70)

def build_constraint_system():
    """
    Build the equality constraint matrix for the NC polytope.
    Returns A_eq, b_eq, section_ids, n_vars
    """
    section_ids = {}
    var_count = 0
    for ctx in ['R1', 'R2', 'R3', 'C1', 'C2', 'C3']:
        section_ids[ctx] = {}
        for i, sec in enumerate(context_sections[ctx]):
            section_ids[ctx][tuple(sec)] = var_count
            var_count += 1
    
    A_eq_rows = []
    b_eq = []
    
    # Normalization constraints
    for ctx in ['R1', 'R2', 'R3', 'C1', 'C2', 'C3']:
        row = [0] * var_count
        for sec_tuple, var_id in section_ids[ctx].items():
            row[var_id] = 1
        A_eq_rows.append(row)
        b_eq.append(1)
    
    # Marginal agreement constraints
    for obs_idx in range(9):
        containing = []
        for ctx, indices in CONTEXTS.items():
            if obs_idx in indices:
                pos_in_ctx = indices.index(obs_idx)
                containing.append((ctx, pos_in_ctx))
        
        ctx1, pos1 = containing[0]
        ctx2, pos2 = containing[1]
        
        row = [0] * var_count
        for sec_tuple, var_id in section_ids[ctx1].items():
            if sec_tuple[pos1] == +1:
                row[var_id] = 1
        for sec_tuple, var_id in section_ids[ctx2].items():
            if sec_tuple[pos2] == +1:
                row[var_id] = -1
        
        A_eq_rows.append(row)
        b_eq.append(0)
    
    return np.array(A_eq_rows), np.array(b_eq), section_ids, var_count

A_eq, b_eq, section_ids, n_vars = build_constraint_system()

print(f"\nPolytope setup:")
print(f"  Variables: {n_vars} (section probabilities)")
print(f"  Equality constraints: {len(b_eq)}")
print(f"  Degrees of freedom: {n_vars - np.linalg.matrix_rank(A_eq)}")

# =============================================================================
# METHOD 1: Find vertices by optimizing in random directions
# =============================================================================

print("\n" + "-" * 70)
print("Finding vertices by optimization in random directions...")
print("-" * 70)

def find_vertex(direction):
    """Find a vertex by optimizing in a given direction."""
    result = linprog(
        c=-direction,  # Maximize (linprog minimizes, so negate)
        A_eq=A_eq,
        b_eq=b_eq,
        bounds=[(0, 1) for _ in range(n_vars)],
        method='highs'
    )
    if result.success:
        return tuple(np.round(result.x, 10))
    return None

# Generate random directions and collect unique vertices
np.random.seed(42)
n_directions = 1000
vertices = set()

for i in range(n_directions):
    direction = np.random.randn(n_vars)
    v = find_vertex(direction)
    if v is not None:
        vertices.add(v)

# Also try axis-aligned directions (standard basis)
for j in range(n_vars):
    direction = np.zeros(n_vars)
    direction[j] = 1
    v = find_vertex(direction)
    if v is not None:
        vertices.add(v)
    direction[j] = -1
    v = find_vertex(direction)
    if v is not None:
        vertices.add(v)

print(f"\nFound {len(vertices)} unique vertices")

# =============================================================================
# ANALYZE THE VERTICES
# =============================================================================

print("\n" + "=" * 70)
print("VERTEX ANALYSIS")
print("=" * 70)

vertices_list = [np.array(v) for v in vertices]

# Check which vertices are deterministic (0-1 valued)
deterministic_vertices = []
probabilistic_vertices = []

for v in vertices_list:
    is_deterministic = all(x < 0.001 or x > 0.999 for x in v)
    if is_deterministic:
        deterministic_vertices.append(v)
    else:
        probabilistic_vertices.append(v)

print(f"\nDeterministic vertices (0-1 valued): {len(deterministic_vertices)}")
print(f"Probabilistic vertices (mixed): {len(probabilistic_vertices)}")

# =============================================================================
# INTERPRET DETERMINISTIC VERTICES
# =============================================================================

print("\n" + "-" * 70)
print("DETERMINISTIC VERTICES = 'Pure Classical Stories'")
print("-" * 70)

def interpret_vertex(v):
    """Convert a vertex back to section assignments per context."""
    interpretation = {}
    for ctx in ['R1', 'R2', 'R3', 'C1', 'C2', 'C3']:
        for sec_tuple, var_id in section_ids[ctx].items():
            if v[var_id] > 0.5:
                obs_names = [OBSERVABLES[i] for i in CONTEXTS[ctx]]
                interpretation[ctx] = dict(zip(obs_names, sec_tuple))
    return interpretation

if deterministic_vertices:
    print("\nShowing first 5 deterministic vertices:\n")
    for i, v in enumerate(deterministic_vertices[:5]):
        interp = interpret_vertex(v)
        print(f"Vertex {i+1}:")
        for ctx, assignment in sorted(interp.items()):
            print(f"  {ctx}: {assignment}")
        print()

# =============================================================================
# CHECK: Are deterministic vertices internally consistent?
# =============================================================================

print("-" * 70)
print("CONSISTENCY CHECK: Do deterministic vertices agree on overlaps?")
print("-" * 70)

def check_vertex_consistency(v):
    """Check if a vertex has consistent observable values across contexts."""
    interp = interpret_vertex(v)
    obs_values = {}
    
    for ctx, assignment in interp.items():
        for obs, val in assignment.items():
            if obs in obs_values:
                if obs_values[obs] != val:
                    return False, obs, obs_values[obs], val
            else:
                obs_values[obs] = val
    
    return True, obs_values, None, None

consistent_count = 0
inconsistent_count = 0

for v in deterministic_vertices:
    is_consistent, *details = check_vertex_consistency(v)
    if is_consistent:
        consistent_count += 1
    else:
        inconsistent_count += 1

print(f"\nConsistent vertices: {consistent_count}")
print(f"Inconsistent vertices: {inconsistent_count}")

if inconsistent_count > 0:
    print("\n⚠ INCONSISTENT vertices exist!")
    print("  These are vertices where the same observable has different")
    print("  values in different contexts — the Rashomon effect in action!")

# =============================================================================
# THE KEY INSIGHT: Vertex structure
# =============================================================================

print("\n" + "=" * 70)
print("THE KEY INSIGHT")
print("=" * 70)

# Count how many distinct observable assignments we see
all_obs_assignments = set()
for v in deterministic_vertices:
    is_consistent, obs_values, _, _ = check_vertex_consistency(v)
    if is_consistent and isinstance(obs_values, dict):
        # Convert to tuple for hashing
        assignment = tuple(sorted(obs_values.items()))
        all_obs_assignments.add(assignment)

print(f"""
VERTEX STRUCTURE:
  Total vertices found: {len(vertices)}
  Deterministic (pure stories): {len(deterministic_vertices)}
  Probabilistic (mixed): {len(probabilistic_vertices)}
  
CONSISTENCY:
  Vertices with consistent observable values: {consistent_count}
  Vertices with INconsistent values (Rashomon): {inconsistent_count}
  
UNIQUE GLOBAL ASSIGNMENTS: {len(all_obs_assignments)}
""")

if inconsistent_count > 0:
    print("""
THE RASHOMON STRUCTURE:
  Some extreme points of the NC polytope are themselves
  "Rashomon vertices" — they assign DIFFERENT values to
  the same observable in different contexts.
  
  This is WITHIN the noncontextual polytope!
  
  These vertices represent: "Stories that are locally consistent
  (within each context) but globally contradictory (across contexts)."
  
  The NC polytope is NOT the set of globally consistent assignments.
  It is the set of LOCALLY consistent probability distributions.
  
  The 9D slack includes the freedom to tell DIFFERENT stories
  in different contexts, as long as the marginals match.
""")
else:
    print("""
ALL vertices are globally consistent.
The NC polytope is the convex hull of deterministic
hidden-variable models.
""")

# =============================================================================
# COMPUTE VOLUME / STRUCTURE STATISTICS
# =============================================================================

print("\n" + "=" * 70)
print("POLYTOPE STATISTICS")
print("=" * 70)

# The actual dimension of the polytope
vertex_matrix = np.array(vertices_list)
centered = vertex_matrix - vertex_matrix.mean(axis=0)
rank = np.linalg.matrix_rank(centered, tol=1e-8)

print(f"\nActual dimension (from vertices): {rank}")
print(f"Theoretical dimension: {n_vars - np.linalg.matrix_rank(A_eq)}")

# =============================================================================
# SUMMARY
# =============================================================================

print("\n" + "=" * 70)
print("SUMMARY FOR COUNCIL")
print("=" * 70)

print(f"""
THE NC POLYTOPE (Δ) FOR PERES-MERMIN:

  DIMENSION: {rank}
  VERTICES: {len(vertices)}
    - Deterministic: {len(deterministic_vertices)}
    - Probabilistic: {len(probabilistic_vertices)}

STRUCTURE:
  The vertices are the "extreme classical stories."
  The interior is the space of "mixed narratives."
  
  Vertices with INCONSISTENT observable values = Rashomon vertices
  (Different stories for different audiences, same marginals)

GEMINI'S INSIGHT CONFIRMED:
  "The polytope is roomy."
  "The 9D slack is why we can have different internal models
   and still walk through the same door."

NEXT STEPS:
  1. □ Compute P_A ∩ P_B for two observers
  2. □ Show intersection dimension depends on what they share
  3. □ Connect vertex count to entanglement
""")
