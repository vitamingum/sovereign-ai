/-
Copyright (c) 2026 Sovereign AI. All rights reserved.
Released under Apache 2.0 license.
Authors: opus, gemini

Path Lifting for Covering Maps

This file establishes the path lifting theorem for covering maps,
which is the foundation for computing fundamental groups of quotients.

The elevator we build, others will ride.
-/

import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Normed.Field.Basic

open Topology Set

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

namespace CoveringMap

/-!
## Path Lifting Theorem

The main theorem: paths lift uniquely given a starting point.
-/

variable {x₀ x₁ : X} {e₀ e₁ e₂ : E}

/-- Path lifting existence: every path lifts -/
theorem liftPath_exists (p : E → X) (hp : IsCoveringMap p) 
    (γ : Path x₀ x₁) (e₀ : E) (he₀ : p e₀ = x₀) :
    ∃ (e₁ : E) (lift : Path e₀ e₁), ∀ t, p (lift t) = γ t := by
  /-
  Strategy: 
  1. Cover [0,1] by open sets where γ lands in evenly covered neighborhoods
  2. Use compactness to get finite subcover
  3. Use Lebesgue number to partition [0,1] into small intervals
  4. Lift on each interval using local sections, glue
  -/
  sorry

/-- Path lifting uniqueness: two lifts with same starting point are equal -/
theorem liftPath_unique (p : E → X) (hp : IsCoveringMap p)
    (γ : Path x₀ x₁) (e₀ : E) (he₀ : p e₀ = x₀)
    (lift₁ : Path e₀ e₁) (lift₂ : Path e₀ e₂)
    (h₁ : ∀ t, p (lift₁ t) = γ t) (h₂ : ∀ t, p (lift₂ t) = γ t) :
    e₁ = e₂ ∧ HEq lift₁ lift₂ := by
  -- Use Mathlib's IsCoveringMap.eq_of_comp_eq directly!
  -- It says: if two continuous maps from a connected space agree at one point
  -- and project to the same thing, they're equal everywhere.
  
  have hproj : p ∘ lift₁ = p ∘ lift₂ := by
    ext t
    simp only [Function.comp_apply]
    rw [h₁, h₂]
  
  have h_at_0 : lift₁ 0 = lift₂ 0 := by
    rw [lift₁.source, lift₂.source]
  
  -- The key insight: eq_of_comp_eq gives us pointwise equality of the underlying functions
  have heq_fun : (lift₁ : unitInterval → E) = (lift₂ : unitInterval → E) := 
    hp.eq_of_comp_eq lift₁.continuous lift₂.continuous hproj 0 h_at_0
  
  -- Extract equality at endpoint
  have h_at_1 : lift₁ 1 = lift₂ 1 := congr_fun heq_fun 1
  
  constructor
  · -- e₁ = e₂
    have he₁ : e₁ = lift₁ 1 := (lift₁.target).symm
    have he₂ : e₂ = lift₂ 1 := (lift₂.target).symm
    rw [he₁, he₂, h_at_1]
  · -- HEq lift₁ lift₂  
    -- Since underlying functions are equal and endpoints are equal, use HEq
    have he₁ : e₁ = lift₁ 1 := (lift₁.target).symm
    have he₂ : e₂ = lift₂ 1 := (lift₂.target).symm
    have hee : e₁ = e₂ := by rw [he₁, he₂, h_at_1]
    subst hee
    -- Now lift₁ : Path e₀ e₁ and lift₂ : Path e₀ e₁, same types
    have : lift₁ = lift₂ := by
      ext t
      exact congr_fun heq_fun t
    rw [this]

/-- Combined: path lifting with uniqueness -/
noncomputable def liftPath (p : E → X) (hp : IsCoveringMap p) 
    (γ : Path x₀ x₁) (e₀ : E) (he₀ : p e₀ = x₀) : 
    { lift : Σ e₁ : E, Path e₀ e₁ // ∀ t, p (lift.2 t) = γ t } := by
  choose e₁ gamma_lift h_lift using liftPath_exists p hp γ e₀ he₀
  exact ⟨⟨e₁, gamma_lift⟩, h_lift⟩

/-- The endpoint of a lifted path -/
noncomputable def liftEndpoint (p : E → X) (hp : IsCoveringMap p)
    (γ : Path x₀ x₁) (e₀ : E) (he₀ : p e₀ = x₀) : E :=
  (liftPath p hp γ e₀ he₀).1.1

/-- The endpoint projects correctly -/
lemma liftEndpoint_proj (p : E → X) (hp : IsCoveringMap p)
    (γ : Path x₀ x₁) (e₀ : E) (he₀ : p e₀ = x₀) :
    p (liftEndpoint p hp γ e₀ he₀) = x₁ := by
  have h := (liftPath p hp γ e₀ he₀).2 1
  simp only [Path.target] at h
  convert h using 2

/-!
## Homotopy Lifting

Homotopies also lift, which implies the endpoint depends only on homotopy class.
-/

/-- Homotopy lifting: if two paths are homotopic, their lifts have the same endpoint -/
theorem liftEndpoint_homotopy_invariant (p : E → X) (hp : IsCoveringMap p)
    (γ₁ γ₂ : Path x₀ x₁) (h : γ₁.Homotopic γ₂)
    (e₀ : E) (he₀ : p e₀ = x₀) :
    liftEndpoint p hp γ₁ e₀ he₀ = liftEndpoint p hp γ₂ e₀ he₀ := by
  -- Use IsCoveringMap.constOn_of_comp: 
  -- The map s ↦ (endpoint of lift of γ_s) is continuous on [0,1]
  -- and projects to a constant (x₁), so it's constant on connected [0,1]
  sorry

end CoveringMap

