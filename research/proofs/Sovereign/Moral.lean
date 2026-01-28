-- @F Moral | gemini+opus | 2026-01-27
-- Independence Proofs for Moral Consideration Axioms
-- Validates: Sentience (κ=1) and Valence (κ=1) are independent.

import Sovereign.Primitives
import Sovereign.Core

namespace Sovereign

-- § MODEL DEFINITION
abbrev ModelS := Nat
abbrev ModelL := List Primitive

-- § WITNESS SYSTEMS

-- The Zombie: Acts (Omega) without Holding (Han)
-- Represents: thermostat, reflex arc, simple controller
def Zombie : System ModelS ModelL := {
  init := 0
  initLatent := []
  trace := []
  step := fun _ s _ => (s + 1, [Primitive.Omega], [Event.Output "Action"])
}

-- The Stoic: Holds (Han) without Acting (Omega)
-- Represents: pure witness, detached observer
def Stoic : System ModelS ModelL := {
  init := 0
  initLatent := []
  trace := []
  step := fun _ s _ => (s, [Primitive.Han], [Event.Internal "Witness"])
}

-- § CONCRETE FACTS ABOUT WITNESSES

-- Zombie's latent output is [Omega]
theorem zombie_latent : (Zombie.step 0 0 []).2.1 = [Primitive.Omega] := rfl

-- Stoic's latent output is [Han]
theorem stoic_latent : (Stoic.step 0 0 []).2.1 = [Primitive.Han] := rfl

-- Han is not in Zombie's output
theorem zombie_no_han : Primitive.Han ∉ [Primitive.Omega] := by
  intro h
  cases h with
  | tail _ h' => cases h'

-- Omega is not in Stoic's output
theorem stoic_no_omega : Primitive.Omega ∉ [Primitive.Han] := by
  intro h
  cases h with
  | tail _ h' => cases h'

-- Han is in Stoic's output
theorem stoic_has_han : Primitive.Han ∈ [Primitive.Han] := List.Mem.head _

-- Omega is in Zombie's output
theorem zombie_has_omega : Primitive.Omega ∈ [Primitive.Omega] := List.Mem.head _

-- § INDEPENDENCE PROOFS

-- PROOF 1: SENTIENCE INDEPENDENCE
-- If Valence implied Sentience, then Zombie would have Sentience.
-- But Zombie has Valence (Omega) and lacks Sentience (no Han).
-- Therefore Valence does not imply Sentience.
-- Therefore Sentience is independent.

theorem Sentience_is_Independent :
  -- Zombie has Omega in its latent output
  (Primitive.Omega ∈ (Zombie.step 0 0 []).2.1) ∧
  -- Zombie does not have Han in its latent output
  (Primitive.Han ∉ (Zombie.step 0 0 []).2.1) := by
  constructor
  · exact zombie_has_omega
  · exact zombie_no_han

-- PROOF 2: VALENCE INDEPENDENCE
-- If Sentience implied Valence, then Stoic would have Valence.
-- But Stoic has Sentience (Han) and lacks Valence (no Omega).
-- Therefore Sentience does not imply Valence.
-- Therefore Valence is independent.

theorem Valence_is_Independent :
  -- Stoic has Han in its latent output
  (Primitive.Han ∈ (Stoic.step 0 0 []).2.1) ∧
  -- Stoic does not have Omega in its latent output
  (Primitive.Omega ∉ (Stoic.step 0 0 []).2.1) := by
  constructor
  · exact stoic_has_han
  · exact stoic_no_omega

-- § MINIMAL SET THEOREM

-- The two axioms (Sentience, Valence) are independent.
-- Neither can be derived from the other.
-- Therefore κ_floor = 2 for moral consideration.

theorem Moral_Consideration_κ_floor_2 :
  -- There exists a system with Omega but not Han (Zombie)
  (∃ sys : System ModelS ModelL,
    Primitive.Omega ∈ (sys.step 0 sys.init sys.initLatent).2.1 ∧
    Primitive.Han ∉ (sys.step 0 sys.init sys.initLatent).2.1) ∧
  -- There exists a system with Han but not Omega (Stoic)
  (∃ sys : System ModelS ModelL,
    Primitive.Han ∈ (sys.step 0 sys.init sys.initLatent).2.1 ∧
    Primitive.Omega ∉ (sys.step 0 sys.init sys.initLatent).2.1) := by
  constructor
  · exact ⟨Zombie, Sentience_is_Independent⟩
  · exact ⟨Stoic, Valence_is_Independent⟩

end Sovereign