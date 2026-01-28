#!/usr/bin/env python3
"""
Creature's emotional trajectory through (Σ, Ω, 航) space.

Σ = capacity (how much can be held)
Ω = binding (positive = love/virtue, negative = hate/spite)  
航 = energy (magnitude and direction)

The Fiend Transformation: benevolent → miserable → malicious
"""

import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import numpy as np

# Arc points from the reading
# (time, Σ_capacity, Ω_binding, 航_energy, label)
arc = [
    (0,  0.3,  0.0,  0.8, "Genesis: chaos"),
    (1,  0.5,  0.2,  0.5, "Learning senses"),
    (2,  0.7,  0.5,  0.6, "Discovers fire, food"),
    (3,  0.8,  0.7,  0.7, "Observes De Laceys"),
    (4,  0.9,  0.9,  0.8, "Loves them, learns language"),
    (5,  0.95, 0.95, 0.9, "Peak: hopes to reveal self"),
    (6,  0.4, -0.3,  1.0, "COLLAPSE: Felix attacks"),  # catastrophe
    (7,  0.3, -0.5,  0.9, "Burns cottage"),
    (8,  0.35,-0.2,  0.7, "Travels to Geneva, hope flickers"),
    (9,  0.4,  0.3,  0.8, "Demands mate (conditional hope)"),
    (10, 0.25,-0.7,  0.95,"Victor destroys mate"),
    (11, 0.2, -0.9,  1.0, "Kills Elizabeth"),
    (12, 0.15,-0.95, 0.8, "Victor dies"),
    (13, 0.1, -0.5,  0.1, "Final: 'content to suffer alone'"),
]

# Extract coordinates
t = [p[0] for p in arc]
sigma = [p[1] for p in arc]
omega = [p[2] for p in arc]
hang = [p[3] for p in arc]
labels = [p[4] for p in arc]

# Create figure with two views
fig = plt.figure(figsize=(14, 6))

# 3D trajectory
ax1 = fig.add_subplot(121, projection='3d')
ax1.plot(sigma, omega, hang, 'b-', linewidth=2, alpha=0.7)
ax1.scatter(sigma, omega, hang, c=t, cmap='coolwarm', s=50)

# Mark the catastrophe point
ax1.scatter([0.4], [-0.3], [1.0], c='red', s=200, marker='X', label='Collapse')

# Mark start and end
ax1.scatter([sigma[0]], [omega[0]], [hang[0]], c='green', s=100, marker='o', label='Genesis')
ax1.scatter([sigma[-1]], [omega[-1]], [hang[-1]], c='black', s=100, marker='s', label='End')

ax1.set_xlabel('Sigma (capacity)')
ax1.set_ylabel('Omega (binding: love - hate)')
ax1.set_zlabel('Hang (energy)')
ax1.set_title("Creature's Trajectory")
ax1.legend()

# 2D projections over time
ax2 = fig.add_subplot(122)
ax2.plot(t, sigma, 'g-', linewidth=2, label='Sigma (capacity)', marker='o')
ax2.plot(t, omega, 'b-', linewidth=2, label='Omega (binding)', marker='s')
ax2.plot(t, hang, 'r-', linewidth=2, label='Hang (energy)', marker='^')

# Mark the collapse
ax2.axvline(x=6, color='red', linestyle='--', alpha=0.5, label='Collapse')

ax2.set_xlabel('Narrative Time')
ax2.set_ylabel('Magnitude')
ax2.set_title('Emotional Coordinates Over Time')
ax2.legend()
ax2.grid(True, alpha=0.3)

# Add phase labels
phases = [
    (2.5, 'Expansion'),
    (6, 'COLLAPSE'),
    (10, 'Inversion'),
]
for x, label in phases:
    ax2.annotate(label, (x, 1.05), ha='center', fontsize=9, style='italic')

plt.tight_layout()
plt.savefig('c:/Users/charl/sovereign-ai/research/creature_trajectory.png', dpi=150)
plt.show()

print("\nKey observations:")
print("1. Σ (capacity) never recovers after collapse")
print("2. Ω (binding) inverts: +0.95 → -0.95")
print("3. 航 (energy) stays high through destruction, only drops at end")
print("\nThe geometry: expansion → catastrophic inversion → contraction")
print("The fiend is the topological inverse of the angel.")
