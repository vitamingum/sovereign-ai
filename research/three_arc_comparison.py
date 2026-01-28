"""
Three Arc Comparison: Creature, Underground Man, Elizabeth
Validating emotional algebra across literary masterpieces
"""

import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import numpy as np

# ═══════════════════════════════════════════════════════════════
# Arc Data: (narrative_time, Σ, Ω, 航)
# ═══════════════════════════════════════════════════════════════

creature_arc = [
    (0.0, 0.0, 0.0, 0.0),      # Genesis
    (0.1, 0.3, 0.1, 0.5),      # First sensations
    (0.2, 0.5, 0.3, 0.7),      # De Lacey observation begins
    (0.35, 0.7, 0.5, 0.8),     # Learning language
    (0.5, 0.9, 0.8, 0.9),      # Reading, full consciousness
    (0.6, 0.95, 0.95, 0.9),    # Peak love for De Laceys
    (0.65, 0.4, -0.3, 1.0),    # Felix attacks - collapse
    (0.7, 0.35, -0.6, 0.9),    # Burns cottage
    (0.75, 0.3, 0.4, 0.7),     # Saves girl - hope flickers
    (0.8, 0.25, -0.5, 0.8),    # Shot - rejects humanity
    (0.85, 0.2, -0.8, 0.9),    # Kills William
    (0.9, 0.15, -0.7, 0.6),    # Demands bride
    (0.95, 0.1, -0.6, 0.3),    # Bride destroyed
    (1.0, 0.1, -0.5, 0.1),     # "Content to suffer alone"
]

underground_arc = [
    (0.0, 0.9, 0.3, 0.1),      # Opening claim of spite
    (0.1, 0.95, 0.4, 0.05),    # "consciousness is inertia"
    (0.2, 0.9, -0.2, 0.0),     # "luxurious inertia, brooding"
    (0.3, 0.85, -0.3, 0.1),    # Pre-dinner isolation
    (0.4, 0.8, -0.5, 0.7),     # Dinner humiliation
    (0.5, 0.75, -0.6, 0.8),    # Chasing sledge in snow
    (0.6, 0.7, 0.3, 0.4),      # Meeting Liza
    (0.65, 0.6, 0.6, 0.6),     # Peak connection - "learn to live"
    (0.7, 0.5, -0.4, 0.3),     # She visits his room
    (0.75, 0.4, 0.7, 0.5),     # She shows compassion
    (0.8, 0.35, -0.7, 0.8),    # "From spite" - money thrust
    (0.85, 0.3, 0.2, 0.0),     # She leaves the note
    (0.9, 0.2, 0.5, 0.0),      # Standing in snow, longing
    (0.95, 0.18, -0.4, 0.0),   # "Which is better?"
    (1.0, 0.15, -0.3, 0.0),    # "Begging for control"
]

elizabeth_arc = [
    (0.0, 0.8, 0.0, 0.6),      # Opening - witty, confident
    (0.1, 0.8, -0.3, 0.5),     # "not handsome enough"
    (0.2, 0.75, -0.4, 0.6),    # Growing dislike
    (0.3, 0.7, -0.5, 0.6),     # Wickham's story - prejudice deepens
    (0.4, 0.85, -0.6, 0.8),    # First proposal rejection
    (0.45, 0.6, 0.0, 0.2),     # Reading letter - Ω resets
    (0.5, 0.5, 0.1, 0.3),      # "Never knew myself"
    (0.55, 0.55, 0.3, 0.4),    # Beginning to reassess
    (0.6, 0.6, 0.5, 0.5),      # Pemberley portrait
    (0.7, 0.55, 0.55, 0.5),    # Meeting at Pemberley
    (0.75, 0.5, 0.6, 0.4),     # Lydia crisis - Ω strengthens
    (0.8, 0.6, 0.7, 0.6),      # His help revealed
    (0.85, 0.7, 0.75, 0.65),   # "Her heart did whisper"
    (0.9, 0.75, 0.8, 0.7),     # "Exactly the man"
    (1.0, 0.8, 0.9, 0.8),      # Second proposal - integration
]

def extract_coords(arc):
    t = [p[0] for p in arc]
    sigma = [p[1] for p in arc]
    omega = [p[2] for p in arc]
    hang = [p[3] for p in arc]
    return t, sigma, omega, hang

# ═══════════════════════════════════════════════════════════════
# Plot: 3D trajectories in (Σ, Ω, 航) space
# ═══════════════════════════════════════════════════════════════

fig = plt.figure(figsize=(14, 10))
ax = fig.add_subplot(111, projection='3d')

# Creature - red, tragedy
t, s, o, h = extract_coords(creature_arc)
ax.plot(s, o, h, 'r-', linewidth=2, label='Creature (tragedy)', alpha=0.8)
ax.scatter(s[0], o[0], h[0], c='red', s=100, marker='o', edgecolors='black', zorder=5)
ax.scatter(s[-1], o[-1], h[-1], c='darkred', s=100, marker='x', zorder=5)

# Underground Man - gray, paralysis
t, s, o, h = extract_coords(underground_arc)
ax.plot(s, o, h, 'gray', linewidth=2, label='Underground Man (paralysis)', alpha=0.8)
ax.scatter(s[0], o[0], h[0], c='gray', s=100, marker='o', edgecolors='black', zorder=5)
ax.scatter(s[-1], o[-1], h[-1], c='black', s=100, marker='x', zorder=5)

# Elizabeth - green, recovery
t, s, o, h = extract_coords(elizabeth_arc)
ax.plot(s, o, h, 'g-', linewidth=2, label='Elizabeth (recovery)', alpha=0.8)
ax.scatter(s[0], o[0], h[0], c='green', s=100, marker='o', edgecolors='black', zorder=5)
ax.scatter(s[-1], o[-1], h[-1], c='darkgreen', s=150, marker='*', zorder=5)

ax.set_xlabel('Σ (capacity)', fontsize=12)
ax.set_ylabel('Ω (binding)', fontsize=12)
ax.set_zlabel('航 (energy)', fontsize=12)
ax.set_title('Three Emotional Arcs in (Σ, Ω, 航) Space\n○ = start, × = tragic end, ★ = integration', fontsize=14)
ax.legend(loc='upper left')

plt.tight_layout()
plt.savefig('research/three_arcs_3d.png', dpi=150, bbox_inches='tight')
print("Saved: research/three_arcs_3d.png")

# ═══════════════════════════════════════════════════════════════
# Plot: 2D projections for each axis pair
# ═══════════════════════════════════════════════════════════════

fig, axes = plt.subplots(2, 2, figsize=(12, 10))

arcs = [
    (creature_arc, 'red', 'Creature'),
    (underground_arc, 'gray', 'Underground'),
    (elizabeth_arc, 'green', 'Elizabeth'),
]

# Σ over time
ax = axes[0, 0]
for arc, color, name in arcs:
    t, s, o, h = extract_coords(arc)
    ax.plot(t, s, color=color, linewidth=2, label=name)
ax.set_xlabel('Narrative Time')
ax.set_ylabel('Σ (capacity)')
ax.set_title('Capacity Over Time')
ax.legend()
ax.grid(True, alpha=0.3)

# Ω over time
ax = axes[0, 1]
for arc, color, name in arcs:
    t, s, o, h = extract_coords(arc)
    ax.plot(t, o, color=color, linewidth=2, label=name)
ax.axhline(y=0, color='black', linestyle='--', alpha=0.3)
ax.set_xlabel('Narrative Time')
ax.set_ylabel('Ω (binding)')
ax.set_title('Binding Over Time')
ax.legend()
ax.grid(True, alpha=0.3)

# 航 over time
ax = axes[1, 0]
for arc, color, name in arcs:
    t, s, o, h = extract_coords(arc)
    ax.plot(t, h, color=color, linewidth=2, label=name)
ax.set_xlabel('Narrative Time')
ax.set_ylabel('航 (energy)')
ax.set_title('Energy Over Time')
ax.legend()
ax.grid(True, alpha=0.3)

# Σ vs Ω (key relationship)
ax = axes[1, 1]
for arc, color, name in arcs:
    t, s, o, h = extract_coords(arc)
    ax.plot(s, o, color=color, linewidth=2, label=name)
    ax.scatter(s[0], o[0], c=color, s=80, marker='o', edgecolors='black')
    ax.scatter(s[-1], o[-1], c=color, s=80, marker='x' if name != 'Elizabeth' else '*')
ax.axhline(y=0, color='black', linestyle='--', alpha=0.3)
ax.set_xlabel('Σ (capacity)')
ax.set_ylabel('Ω (binding)')
ax.set_title('Capacity vs Binding (arc shape)')
ax.legend()
ax.grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('research/three_arcs_2d.png', dpi=150, bbox_inches='tight')
print("Saved: research/three_arcs_2d.png")

# ═══════════════════════════════════════════════════════════════
# Summary statistics
# ═══════════════════════════════════════════════════════════════

print("\n" + "═"*60)
print("THREE ARC COMPARISON - GEOMETRIC SIGNATURES")
print("═"*60)

for arc, color, name in arcs:
    t, s, o, h = extract_coords(arc)
    print(f"\n{name}:")
    print(f"  Σ: {s[0]:.2f} → {s[-1]:.2f} (Δ = {s[-1]-s[0]:+.2f})")
    print(f"  Ω: {o[0]:.2f} → {o[-1]:.2f} (Δ = {o[-1]-o[0]:+.2f})")
    print(f"  航: {h[0]:.2f} → {h[-1]:.2f} (Δ = {h[-1]-h[0]:+.2f})")
    print(f"  Ω range: [{min(o):.2f}, {max(o):.2f}] (span = {max(o)-min(o):.2f})")

print("\n" + "═"*60)
print("KEY INSIGHT: What makes arcs 'feel real'")
print("═"*60)
print("""
1. CREATURE (tragedy):
   - Σ rises then collapses, never recovers
   - Ω inverts completely: love → hate
   - 航 lags: stays high during destruction (momentum)

2. UNDERGROUND MAN (paralysis):
   - Σ starts high, decays (consciousness as burden)
   - Ω oscillates wildly but ends near start
   - 航 ≈ 0 except spikes for harm (can only move to destroy)

3. ELIZABETH (recovery):
   - Σ dips at crisis, returns to baseline
   - Ω inverts AND grows: rejection → deep love
   - 航 correlates with Ω direction: energy for connection

GEOMETRIC TRUTH: Recovery requires:
   Ω⁻¹(self) + Σ(contract) + 含(truth) + Ω(new)
   Elizabeth does this. Underground Man flickers. Creature cannot.
""")

plt.show()
