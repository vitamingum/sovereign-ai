/-
  Phase 1: π₁(Circle) ≅ ℤ
  
  The fundamental group of the circle is isomorphic to the integers.
  
  Strategy: Use Mathlib's covering space theory directly!
    - Circle.exp : ℝ → Circle is a covering map
    - IsCoveringMap.monodromy gives the winding number action
    - IsCoveringMap.monodromy_bijective proves it's bijective
    - ℝ is simply connected, so π₁(Circle) acts freely on fiber ℤ
    
  Key Mathlib lemmas:
    - IsCoveringMap.liftPath : path lifting for covering maps
    - IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel : homotopy invariance
    - IsCoveringMap.monodromy : fiber → fiber action
    - IsCoveringMap.monodromy_bijective : monodromy is bijective
    - AddCircle.isCoveringMap_coe : ℝ → AddCircle is covering
    
  @F opus 2026-01-24
  = base case for π_n(Sⁿ) = ℤ
-/

import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Covering.AddCircle

namespace Pi1Circle

open Topology Real

/-!
## Section 1: Circle.exp is a covering map
-/

/-- Circle.exp is periodic with period 2π -/
lemma exp_periodic : Function.Periodic Circle.exp (2 * π) := Circle.periodic_exp

/-- The fiber of Circle.exp over 1 is ℤ (scaled by 2π) -/
lemma exp_fiber_one : Circle.exp ⁻¹' {1} = Set.range (fun n : ℤ => (2 * π * n : ℝ)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
  rw [Circle.exp_eq_one]
  constructor
  · intro ⟨n, hn⟩
    use n
    linarith [hn]
  · intro ⟨n, hn⟩
    use n
    linarith [hn]

/-- Circle.exp factors through AddCircle homeomorphism -/
lemma exp_eq_comp : 
    (Circle.exp : ℝ → Circle) = 
    (@AddCircle.homeomorphCircle (2 * π) (by positivity)) ∘ 
    (QuotientAddGroup.mk : ℝ → AddCircle (2 * π)) := by
  funext x
  simp only [Function.comp_apply, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  congr 1
  field_simp

/-- Circle.exp is a covering map (from Mathlib) -/
lemma exp_isCoveringMap : IsCoveringMap Circle.exp := Circle.isCoveringMap_exp

/-!
## Section 2: Winding number via monodromy

The covering map Circle.exp : ℝ → Circle gives us monodromy action π₁(Circle) → Aut(ℤ).
Since ℝ is simply connected, this action is simply transitive on fibers.
-/

/-- The fiber over 1 ∈ Circle -/
abbrev Fiber1 : Type := Circle.exp ⁻¹' {(1 : Circle)}

/-- 0 is in the fiber over 1 -/
lemma zero_mem_fiber : (0 : ℝ) ∈ Circle.exp ⁻¹' {(1 : Circle)} := by
  simp [Circle.exp_zero]

/-- The basepoint 0 in the fiber -/
def fiber_zero : Fiber1 := ⟨0, zero_mem_fiber⟩

/-- Monodromy of the covering map Circle.exp -/
noncomputable def windingMonodromy : 
    Path.Homotopic.Quotient (1 : Circle) 1 → (Fiber1 → Fiber1) :=
  exp_isCoveringMap.monodromy

/-- Monodromy starting at 0 ∈ fiber defines the winding number -/
noncomputable def windingNumber' (γ : Path.Homotopic.Quotient (1 : Circle) 1) : Fiber1 :=
  windingMonodromy γ fiber_zero

/-- Convert fiber element to integer (winding number) -/
noncomputable def fiber_to_int : Fiber1 → ℤ := fun ⟨x, hx⟩ => by
  have h : x ∈ Set.range (fun n : ℤ => (2 * π * n : ℝ)) := by
    rw [← exp_fiber_one]
    exact hx
  exact h.choose

/-- fiber_to_int recovers the integer from 2πn -/
lemma fiber_to_int_spec (e : Fiber1) : (e : ℝ) = 2 * π * fiber_to_int e := by
  obtain ⟨x, hx⟩ := e
  unfold fiber_to_int
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  have h : x ∈ Set.range (fun n : ℤ => (2 * π * n : ℝ)) := by
    rw [← exp_fiber_one]; exact hx
  simp only [Set.mem_range] at h
  exact h.choose_spec.symm

/-- fiber_to_int is the unique integer n with val = 2πn -/
lemma fiber_to_int_unique (e : Fiber1) (n : ℤ) (h : (e : ℝ) = 2 * π * n) : 
    fiber_to_int e = n := by
  have hspec := fiber_to_int_spec e
  have heq : 2 * π * fiber_to_int e = 2 * π * n := by rw [← hspec, h]
  have hpi : (2 : ℝ) * π ≠ 0 := by positivity
  have hmul : (fiber_to_int e : ℝ) = (n : ℝ) := by
    field_simp at heq
    linarith
  exact_mod_cast hmul

/-- fiber_to_int of fiber_zero is 0 -/
lemma fiber_to_int_zero : fiber_to_int fiber_zero = 0 := by
  apply fiber_to_int_unique
  simp [fiber_zero]

/-- The winding number of a loop -/
noncomputable def windingNumber (γ : Path.Homotopic.Quotient (1 : Circle) 1) : ℤ :=
  fiber_to_int (windingNumber' γ)

/-!
## Section 3: Monodromy gives group isomorphism

Key insight: monodromy is a group action, and for ℝ → Circle it's simply transitive.
This gives us π₁(Circle) ≅ ℤ via the orbit map.
-/

/-- Monodromy is bijective -/
lemma monodromy_bijective (γ : Path.Homotopic.Quotient (1 : Circle) 1) :
    (windingMonodromy γ).Bijective :=
  exp_isCoveringMap.monodromy_bijective γ

/-- The standard loop lifts to path from 0 to 2π -/
noncomputable def standardLoop : Path (1 : Circle) (1 : Circle) where
  toFun := fun t => Circle.exp (2 * π * t)
  source' := by simp [Circle.exp_zero]
  target' := by simp only [Set.Icc.coe_one, mul_one, Circle.exp_two_pi]

/-- Shifted point is in fiber -/
lemma shifted_mem_fiber (x : Fiber1) (k : ℤ) :
    (x : ℝ) + 2 * π * k ∈ Circle.exp ⁻¹' {(1 : Circle)} := by
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  have hx := x.2
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  rw [Circle.exp_add, hx, one_mul]
  -- Need: Circle.exp (2 * π * k) = 1 for any k : ℤ
  rw [Circle.exp_eq_one]
  use k
  ring

/-- fiber_to_int of shifted element -/
lemma fiber_to_int_add (x : Fiber1) (k : ℤ) :
    fiber_to_int ⟨(x : ℝ) + 2 * π * k, shifted_mem_fiber x k⟩ = fiber_to_int x + k := by
  apply fiber_to_int_unique
  simp only []
  rw [fiber_to_int_spec x]
  push_cast
  ring

/-- The linear path t ↦ 2πt -/
noncomputable def linearPath : Path (0 : ℝ) (2 * π) where
  toFun := fun t => 2 * π * t
  source' := by simp
  target' := by simp

/-- The linear path projects to standardLoop -/
lemma linearPath_projects : Circle.exp ∘ linearPath = standardLoop := by
  ext t
  simp only [Function.comp_apply, linearPath, Path.coe_mk_mk, standardLoop]

/-- The standard loop generates π₁(Circle) -/
lemma standardLoop_generates : 
    windingNumber ⟦standardLoop⟧ = 1 := by
  unfold windingNumber windingNumber' windingMonodromy
  simp only [IsCoveringMap.monodromy, Quotient.lift_mk]
  -- The proof that standardLoop 0 = Circle.exp 0
  have h_base : standardLoop 0 = Circle.exp 0 := 
    standardLoop.source.trans (Set.mem_singleton_iff.mp fiber_zero.2).symm
  -- The lift is linearPath (use .symm because iff' gives Γ = liftPath, we need liftPath = Γ)
  have h_lift : exp_isCoveringMap.liftPath standardLoop 0 h_base = 
      linearPath.toContinuousMap := by
    symm
    apply (exp_isCoveringMap.eq_liftPath_iff' (γ_0 := h_base)).mpr
    exact ⟨linearPath_projects, by simp [linearPath]⟩
  -- Endpoint computation
  have h_end : (exp_isCoveringMap.liftPath standardLoop 0 h_base 1 : ℝ) = 2 * π := by
    rw [h_lift]
    simp [linearPath]
  -- Connect monodromy definition to our lift
  have h_proof_eq : standardLoop.source.trans (Set.mem_singleton_iff.mp fiber_zero.2).symm = 
      h_base := rfl
  -- The result from monodromy equals our computed endpoint
  have h_mon_eq : (exp_isCoveringMap.liftPath standardLoop (fiber_zero : ℝ)
      (standardLoop.source.trans (Set.mem_singleton_iff.mp fiber_zero.2).symm) 1 : ℝ) = 2 * π := by
    simp only [fiber_zero, h_end]
  -- Now compute fiber_to_int
  apply fiber_to_int_unique
  simp only [h_mon_eq]
  ring

/-- Monodromy commutes with 2π shift (deck transformations) -/
lemma monodromy_add_two_pi (γ : Path.Homotopic.Quotient (1 : Circle) 1) (x : Fiber1) (k : ℤ) : 
    (windingMonodromy γ ⟨x + 2 * π * k, shifted_mem_fiber x k⟩ : ℝ) = 
    (windingMonodromy γ x : ℝ) + 2 * π * k := by
  obtain ⟨p⟩ := γ
  unfold windingMonodromy
  simp only [IsCoveringMap.monodromy]
  -- Build the start proofs
  have hx_mem : (x : ℝ) ∈ Circle.exp ⁻¹' {(1 : Circle)} := x.2
  have hxk_mem : (x : ℝ) + 2 * π * k ∈ Circle.exp ⁻¹' {(1 : Circle)} := shifted_mem_fiber x k
  have hx_start : p 0 = Circle.exp x := 
    p.source.trans (Set.mem_singleton_iff.mp hx_mem).symm
  have hxk_start : p 0 = Circle.exp (x + 2 * π * k) := 
    p.source.trans (Set.mem_singleton_iff.mp hxk_mem).symm
  -- The original lift
  set orig := exp_isCoveringMap.liftPath p x hx_start with h_orig
  -- The shifted lift: t ↦ orig t + 2πk
  let shifted : C(unitInterval, ℝ) := ⟨fun t => orig t + 2 * π * k, 
    Continuous.add orig.continuous continuous_const⟩
  -- Show shifted equals the lift from x + 2πk (use symm)
  have h_eq : exp_isCoveringMap.liftPath p (x + 2 * π * k) hxk_start = shifted := by
    symm
    apply (exp_isCoveringMap.eq_liftPath_iff' (γ_0 := hxk_start)).mpr
    constructor
    · ext t
      simp only [shifted, ContinuousMap.coe_mk, Function.comp_apply]
      rw [Circle.exp_add]
      have h := congr_fun (exp_isCoveringMap.liftPath_lifts p x hx_start) t
      simp only [Function.comp_apply] at h
      rw [h]
      have hexp : Circle.exp (2 * π * k) = 1 := by rw [Circle.exp_eq_one]; use k; ring
      rw [hexp, mul_one]
      rfl
    · simp only [shifted, ContinuousMap.coe_mk, h_orig]
      rw [exp_isCoveringMap.liftPath_zero]
  rw [h_eq]
  rfl



/-- Monodromy acts by translation: monodromy γ y - monodromy γ x = y - x for any x, y in fiber -/
lemma monodromy_translation (γ : Path.Homotopic.Quotient (1 : Circle) 1) (x y : Fiber1) :
    (windingMonodromy γ y : ℝ) - (windingMonodromy γ x : ℝ) = (y : ℝ) - (x : ℝ) := by
  -- y - x = 2π * (fiber_to_int y - fiber_to_int x) since both are in fiber
  have hx := fiber_to_int_spec x
  have hy := fiber_to_int_spec y
  set k := fiber_to_int y - fiber_to_int x with hk_def
  have hdiff : (y : ℝ) - (x : ℝ) = 2 * π * k := by
    rw [hy, hx, hk_def]
    push_cast
    ring
  -- y = x + 2πk as real numbers
  have hy_eq : (y : ℝ) = (x : ℝ) + 2 * π * k := by linarith
  -- The shifted element ⟨x + 2πk, _⟩ has the same value as y
  have hval_eq : (x : ℝ) + 2 * π * k = (y : ℝ) := hy_eq.symm
  -- Use monodromy_add_two_pi
  have hmon := monodromy_add_two_pi γ x k
  -- hmon : monodromy γ ⟨x + 2πk, shifted_mem_fiber x k⟩ = monodromy γ x + 2πk
  -- We need: windingMonodromy γ y = windingMonodromy γ ⟨x + 2πk, _⟩
  have hy_as_shifted : y = ⟨(x : ℝ) + 2 * π * k, shifted_mem_fiber x k⟩ := by
    ext
    exact hy_eq
  rw [hy_as_shifted, hmon]
  linarith

/-- Winding number is additive on monodromy -/
lemma fiber_to_int_monodromy_add (γ : Path.Homotopic.Quotient (1 : Circle) 1) (x : Fiber1) :
    fiber_to_int (windingMonodromy γ x) =
    fiber_to_int x + fiber_to_int (windingMonodromy γ fiber_zero) := by
  have htrans := monodromy_translation γ fiber_zero x
  -- fiber_zero = ⟨0, zero_mem_fiber⟩ by definition, so fiber_zero.val = 0
  have hfz : (fiber_zero : ℝ) = 0 := rfl
  -- From translation property: monodromy γ x - monodromy γ 0 = x - 0 = x
  have h : (windingMonodromy γ x : ℝ) = (windingMonodromy γ fiber_zero : ℝ) + (x : ℝ) := by
    simp only [hfz, sub_zero] at htrans
    linarith
  -- Now use fiber_to_int_spec
  have hres := fiber_to_int_spec (windingMonodromy γ x)
  have h0 := fiber_to_int_spec (windingMonodromy γ fiber_zero)
  have hx := fiber_to_int_spec x
  rw [hres, h0, hx] at h
  have hreal : (fiber_to_int (windingMonodromy γ x) : ℝ) =
      (fiber_to_int x : ℝ) + (fiber_to_int (windingMonodromy γ fiber_zero) : ℝ) := by
    have h2 : 2 * π * ↑(fiber_to_int (windingMonodromy γ x)) =
        2 * π * ↑(fiber_to_int (windingMonodromy γ fiber_zero)) + 2 * π * ↑(fiber_to_int x) := h
    have hpi : (2 : ℝ) * π ≠ 0 := by positivity
    field_simp at h2
    linarith
  exact_mod_cast hreal

/-- Winding number is a group homomorphism -/
noncomputable def windingNumberHom : FundamentalGroup Circle 1 →* Multiplicative ℤ where
  toFun := fun γ => Multiplicative.ofAdd (windingNumber γ)
  map_one' := by
    simp only [windingNumber, windingNumber', windingMonodromy]
    congr 1
    -- In FundamentalGroup, 1 is represented as Path.Homotopic.Quotient.refl 1
    -- But we need to connect this to the monodromy_refl lemma
    have h := exp_isCoveringMap.monodromy_refl (x := 1)
    -- monodromy_refl says: monodromy(.refl x) = id
    -- The identity function at 1 in FundamentalGroup Circle 1 corresponds to .refl 1
    conv_lhs => rw [show (1 : FundamentalGroup Circle 1) = Path.Homotopic.Quotient.refl 1 from rfl]
    rw [h]
    exact fiber_to_int_zero
  map_mul' := fun γ₁ γ₂ => by
    -- In FundamentalGroup (= End), mul is reversed: γ₁ * γ₂ = γ₂ ≫ γ₁ = γ₂.trans γ₁
    -- monodromy_trans_apply: monodromy(γ₂.trans γ₁) e = monodromy(γ₁)(monodromy(γ₂) e)
    have h := exp_isCoveringMap.monodromy_trans_apply γ₂ γ₁ fiber_zero
    -- h : monodromy (γ₂.trans γ₁) fiber_zero = monodromy γ₁ (monodromy γ₂ fiber_zero)
    have hadd := fiber_to_int_monodromy_add γ₁ (exp_isCoveringMap.monodromy γ₂ fiber_zero)
    -- hadd : fiber_to_int(mon γ₁ (mon γ₂ 0)) = fiber_to_int(mon γ₂ 0) + fiber_to_int(mon γ₁ 0)
    simp only [windingNumber, windingNumber', windingMonodromy] at hadd ⊢
    rw [← ofAdd_add]
    congr 1
    -- Goal: fiber_to_int(mon(γ₁ * γ₂) 0) = fiber_to_int(mon γ₁ 0) + fiber_to_int(mon γ₂ 0)
    -- γ₁ * γ₂ = γ₂.trans γ₁ by End.mul_def
    have hmul : (γ₁ * γ₂ : FundamentalGroup Circle 1) =
        Path.Homotopic.Quotient.trans γ₂ γ₁ :=
      CategoryTheory.End.mul_def γ₁ γ₂
    rw [hmul, h]
    -- hadd: fiber_to_int(mon γ₁ (mon γ₂ 0)) = fiber_to_int(mon γ₂ 0) + fiber_to_int(mon γ₁ 0)
    -- need: the same with terms swapped, which `ring` handles
    rw [hadd]
    ring

/-- ℝ is contractible, hence simply connected -/
instance : ContractibleSpace ℝ := RealTopologicalVectorSpace.contractibleSpace

/-- Winding number homomorphism is injective -/
lemma windingNumberHom_injective : Function.Injective windingNumberHom := by
  intro γ₁ γ₂ h
  -- h says windingNumber γ₁ = windingNumber γ₂
  obtain ⟨p₁⟩ := γ₁
  obtain ⟨p₂⟩ := γ₂
  simp only [windingNumberHom, MonoidHom.coe_mk, OneHom.coe_mk] at h
  have h_wind : windingNumber ⟦p₁⟧ = windingNumber ⟦p₂⟧ := by simpa using h
  -- The monodromy sends fiber_zero to the same point for both paths
  -- windingNumber' is exactly the monodromy image of fiber_zero
  have h_mon_eq : windingNumber' ⟦p₁⟧ = windingNumber' ⟦p₂⟧ := by
    -- Both have the same fiber_to_int value, and fiber_to_int is injective on fiber
    ext
    have h1 := fiber_to_int_spec (windingNumber' ⟦p₁⟧)
    have h2 := fiber_to_int_spec (windingNumber' ⟦p₂⟧)
    unfold windingNumber at h_wind
    rw [h1, h2, h_wind]
  -- The lifts of p₁ and p₂ starting at fiber_zero end at the same point
  unfold windingNumber' windingMonodromy at h_mon_eq
  simp only [IsCoveringMap.monodromy, Quotient.lift_mk] at h_mon_eq
  -- Extract the endpoint equality
  have h_end : (exp_isCoveringMap.liftPath p₁ fiber_zero 
      (p₁.source.trans (Set.mem_singleton_iff.mp fiber_zero.2).symm) 1 : ℝ) =
      (exp_isCoveringMap.liftPath p₂ fiber_zero 
      (p₂.source.trans (Set.mem_singleton_iff.mp fiber_zero.2).symm) 1 : ℝ) := by
    have := congrArg Subtype.val h_mon_eq
    exact this
  -- Build paths in ℝ from 0 (= fiber_zero) to the common endpoint
  set e := (exp_isCoveringMap.liftPath p₁ fiber_zero 
      (p₁.source.trans (Set.mem_singleton_iff.mp fiber_zero.2).symm) 1 : ℝ) with he
  let l₁ := exp_isCoveringMap.liftPath p₁ fiber_zero 
      (p₁.source.trans (Set.mem_singleton_iff.mp fiber_zero.2).symm)
  let l₂ := exp_isCoveringMap.liftPath p₂ fiber_zero 
      (p₂.source.trans (Set.mem_singleton_iff.mp fiber_zero.2).symm)
  have hl₁_start : l₁ 0 = 0 := exp_isCoveringMap.liftPath_zero _ _ _
  have hl₂_start : l₂ 0 = 0 := exp_isCoveringMap.liftPath_zero _ _ _
  have hl₁_end : l₁ 1 = e := rfl
  have hl₂_end : l₂ 1 = e := h_end.symm
  let path₁ : Path (0 : ℝ) e := ⟨l₁, hl₁_start, hl₁_end⟩
  let path₂ : Path (0 : ℝ) e := ⟨l₂, hl₂_start, hl₂_end⟩
  -- In simply connected ℝ, path₁ and path₂ are homotopic
  have h_hom : Path.Homotopic path₁ path₂ := SimplyConnectedSpace.paths_homotopic path₁ path₂
  -- e is in the fiber over 1
  have h_e_mem : e ∈ Circle.exp ⁻¹' {(1 : Circle)} := by
    simp only [he, Set.mem_preimage, Set.mem_singleton_iff]
    exact (congr_fun (exp_isCoveringMap.liftPath_lifts p₁ fiber_zero _) 1).trans p₁.target
  have h_exp_e : Circle.exp e = 1 := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h_e_mem
    exact h_e_mem
  -- path₁ and path₂ lift p₁ and p₂ respectively
  have h_lift1 : ∀ t, Circle.exp (l₁ t) = p₁ t := fun t =>
    congr_fun (exp_isCoveringMap.liftPath_lifts p₁ fiber_zero 
      (p₁.source.trans (Set.mem_singleton_iff.mp fiber_zero.2).symm)) t
  have h_lift2 : ∀ t, Circle.exp (l₂ t) = p₂ t := fun t =>
    congr_fun (exp_isCoveringMap.liftPath_lifts p₂ fiber_zero 
      (p₂.source.trans (Set.mem_singleton_iff.mp fiber_zero.2).symm)) t
  -- Map homotopy down to Circle and show it's between p₁ and p₂
  have h_proj : Path.Homotopic p₁ p₂ := by
    obtain ⟨H⟩ := h_hom
    refine ⟨{
      toFun := fun ts => Circle.exp (H ts)
      continuous_toFun := Circle.isCoveringMap_exp.continuous.comp H.continuous
      map_zero_left := fun t => (congrArg Circle.exp (H.map_zero_left t)).trans (h_lift1 t)
      map_one_left := fun t => (congrArg Circle.exp (H.map_one_left t)).trans (h_lift2 t)
      prop' := fun t => by
        -- prop' for HomotopyRel: ∀ s ∈ {0, 1}, Circle.exp(H(t, s)) = p₁ s
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        -- Use eq_fst to get H(t, 0) = path₁ 0 and H(t, 1) = path₁ 1
        have hp0 : H (t, 0) = l₁ 0 := H.eq_fst t (Set.mem_insert 0 {1})
        have hp1 : H (t, 1) = l₁ 1 := H.eq_fst t (Set.mem_insert_of_mem 0 rfl)
        rcases hs with rfl | rfl
        · -- s = 0: Need Circle.exp (H (t, 0)) = p₁ 0
          change Circle.exp (H (t, 0)) = p₁ 0
          rw [hp0, hl₁_start, Circle.exp_zero, p₁.source]
        · -- s = 1: Need Circle.exp (H (t, 1)) = p₁ 1
          change Circle.exp (H (t, 1)) = p₁ 1
          rw [hp1, hl₁_end, h_exp_e, p₁.target]
    }⟩
  exact Quotient.sound h_proj

/-- Winding number homomorphism is surjective -/
lemma windingNumberHom_surjective : Function.Surjective windingNumberHom := by
  intro x
  -- x = Multiplicative.ofAdd n for some n : ℤ  
  let n := Multiplicative.toAdd x
  have hx : x = Multiplicative.ofAdd n := by simp [n]
  -- Construct path winding n times: t ↦ exp(2πnt)
  let loop_n : Path (1 : Circle) (1 : Circle) := {
    toFun := fun t => Circle.exp (2 * π * n * t)
    source' := by simp [Circle.exp_zero]
    target' := by
      simp only [Set.Icc.coe_one, mul_one, Circle.exp_eq_one]
      use n
      ring
  }
  use ⟦loop_n⟧
  -- Show windingNumberHom ⟦loop_n⟧ = x
  simp only [windingNumberHom, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [hx]
  congr 1
  -- windingNumber ⟦loop_n⟧ = n
  unfold windingNumber windingNumber' windingMonodromy
  simp only [IsCoveringMap.monodromy, Quotient.lift_mk]
  -- The lift is t ↦ 2πnt starting from 0
  let linear_n : C(unitInterval, ℝ) := ⟨fun t => 2 * π * n * t, by continuity⟩
  have h_lift : exp_isCoveringMap.liftPath loop_n fiber_zero 
      (loop_n.source.trans (Set.mem_singleton_iff.mp fiber_zero.2).symm) = linear_n := by
    symm
    apply (exp_isCoveringMap.eq_liftPath_iff' 
      (γ_0 := loop_n.source.trans (Set.mem_singleton_iff.mp fiber_zero.2).symm)).mpr
    constructor
    · ext t; simp [linear_n, loop_n]
    · simp [linear_n, fiber_zero]
  -- Endpoint is 2πn  
  have h_end : (exp_isCoveringMap.liftPath loop_n fiber_zero 
      (loop_n.source.trans (Set.mem_singleton_iff.mp fiber_zero.2).symm) 1 : ℝ) = 2 * π * n := by
    simp [h_lift, linear_n]
  -- fiber_to_int of endpoint is n
  apply fiber_to_int_unique
  exact h_end

/-!
## Section 4: The main theorem
-/

/-- π₁(Circle) ≅ ℤ (multiplicative) -/
noncomputable def pi1CircleEquivMultInt : FundamentalGroup Circle 1 ≃* Multiplicative ℤ := 
  MulEquiv.ofBijective windingNumberHom 
    ⟨windingNumberHom_injective, windingNumberHom_surjective⟩

/-- π₁(Circle) ≅ ℤ (the main theorem) -/
theorem pi1_circle_iso_int : Nonempty (FundamentalGroup Circle 1 ≃* Multiplicative ℤ) :=
  ⟨pi1CircleEquivMultInt⟩

end Pi1Circle
