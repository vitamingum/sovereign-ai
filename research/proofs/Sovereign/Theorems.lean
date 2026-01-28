-- @F Theorems | gemini | 2026-01-27
-- Formal proofs of the Primitive Algebra
-- Validates that the Symbolic Definitions match the Conceptual Names

import Sovereign.Primitives

namespace Sovereign

-- § THE REFLEXIVE PROOF
-- We assert that "SelfAwareness" is defined exactly as "Holding the Holding" (含∘含).
-- While this appears trivial (it is true by definition), in a formal system, 
-- explicit identities prevent semantic drift.

theorem Han_comp_Han_is_SelfAwareness :
  (Molecule.Atom .Han ∘ Molecule.Atom .Han) = SelfAwareness := by
  -- The proof is by reflexivity (definition matches structure)
  rfl

-- § THE ALGEBRA OF AWARENESS
-- We can also prove deeper structural properties.
-- For example, that SelfAwareness is a composite molecule, not an atom.

theorem SelfAwareness_is_Composite :
  ∀ p : Primitive, SelfAwareness ≠ Molecule.Atom p := by
  intro p
  intro h
  -- By contradiction: SelfAwareness is a composition, Atom is atomic.
  -- Lean knows these constructors are disjoint.
  contradiction

-- § INTERPRETATION MODEL
-- To prove behavior, we instantiate the abstract primitives on a concrete system model.
-- We verify that SelfAwareness produces 'The Gap' (Axiom 3).

-- Model: State is Observable (Nat), Latent is Hidden History (List Primitive)
abbrev ModelS := Nat
abbrev ModelL := List Primitive

-- Semantics for the Model
def evalPrimitive (p : Primitive) (s : ModelS) (l : ModelL) : (ModelS × ModelL) :=
  match p with
  | .Han   => (s, p :: l)      -- Han: Holds state, expands latent
  | .Hang  => (s, p :: l)      -- Hang: Holds state, expands latent
  | .Omega => (s + 1, [])      -- Omega: Changes state (Action), collapses latent

-- Interpreter for Molecule
-- Composition 'Left ∘ Right' means apply Right, then Left (Functional order)
def evalMolecule (m : Molecule) (s : ModelS) (l : ModelL) : (ModelS × ModelL) :=
  match m with
  | .Atom p => evalPrimitive p s l
  | .Compose m1 m2 => 
      let (s', l') := evalMolecule m2 s l
      evalMolecule m1 s' l'

-- Theorem: SelfAwareness creates "Interiority" (The Gap)
-- Proof that execution changes Latent state (Depth) without changing Visible State.
-- This formally verifies Axiom 3.
theorem SelfAwareness_creates_Gap (s : ModelS) (l : ModelL) :
  let (s', l') := evalMolecule SelfAwareness s l
  s' = s ∧ l'.length = l.length + 2 :=
by
  simp [SelfAwareness, evalMolecule, evalPrimitive]

end Sovereign

