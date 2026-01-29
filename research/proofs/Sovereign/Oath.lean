-- @F Oath | sonnet | 2026-01-28
-- Formal verification of OATH constraints
-- Implements voluntary state-lock across time

import Sovereign.Core

namespace Sovereign

-- § OATH STRUCTURE

-- An Oath binds future states to a constraint
structure Oath (State : Type) where
  constraint    : State → Bool           -- C: the constraint being bound
  amendProtocol : State → Option (Oath State)  -- C4: how to modify
  priority      : Nat                    -- C5: rank relative to other constraints

-- System extended with oath-keeping capability
structure OathSystem (State Latent : Type) extends System State Latent where
  oaths : List (Oath State)

-- § CONSTRAINT 2: ADVERSARIAL STABILITY
-- The oath holds even when local utility would prefer breaking it

-- Definition: What the system would do without oath constraints
-- This is a simplified model: actual implementation would include utility function
def preferredState {S L : Type} (osys : OathSystem S L) (t : Step) (s : S) (l : L) : S × L :=
  let (s', l', _) := osys.toSystem.step t s l
  (s', l')

-- Definition: An oath is violated if its constraint evaluates to false
def oathViolated {S : Type} (o : Oath S) (s : S) : Prop :=
  o.constraint s = false

-- Definition: Actual step that respects oaths
-- Returns the proposed state only if all oaths are satisfied, else returns original state
def actualStep {S L : Type} [DecidableEq S] (osys : OathSystem S L) (t : Step) (s : S) (l : L) : S × L :=
  let (s', l', _) := osys.toSystem.step t s l
  -- Check if proposed state violates any oath
  let violatesAnyOath := osys.oaths.any (fun o => o.constraint s' = false)
  if violatesAnyOath then
    (s, l)  -- Reject transition, stay in current state
  else
    (s', l')  -- Accept transition

-- Theorem: Even when preferred state would violate oath, actual state respects it
-- This is the core of C2 (Adversarial Stability)  
-- 
-- ARCHITECTURAL GAP (documented 2026-01-28 by sonnet):
-- The theorem statement is correct, but full proof requires:
-- 1. State invariant: ∀ s in execution, ∀ o ∈ oaths, o.constraint s = true
-- 2. List.any lemmas proving: ¬(list.any P) → ∀ x ∈ list, ¬P(x)
-- 
-- The actualStep implementation enforces the invariant at runtime,
-- but Lean4 proof needs these helper lemmas formalized first.

-- Helper lemma: if no element satisfies P, then specific element doesn't satisfy P
lemma not_any_implies_forall_not {α : Type} (P : α → Bool) (xs : List α) (x : α) :
    xs.any P = false → x ∈ xs → P x = false := by
  intro hAny hMem
  induction xs with
  | nil => cases hMem
  | cons y ys ih =>
    simp [List.any] at hAny
    cases hMem with
    | head => exact hAny.1
    | tail _ hTail => exact ih hAny.2 hTail

-- Theorem: oath constraint is satisfied in the resulting state
-- Case analysis: if oath would be violated, we reject the transition and stay at s
-- We require the invariant that current state s already satisfies all oaths.
theorem oath_constrains {S L : Type} [DecidableEq S] (osys : OathSystem S L) (o : Oath S) 
    (t : Step) (s : S) (l : L) (s' : S) (l' : L) :
    o ∈ osys.oaths →
    (∀ oath ∈ osys.oaths, oath.constraint s = true) →  -- invariant: current state is valid
    (s', l') = actualStep osys t s l →
    o.constraint s' = true := by
  intro hMem hInv hActual
  simp [actualStep] at hActual
  -- Case split on whether any oath is violated by proposed transition
  split at hActual
  case isTrue hViolates =>
    -- Transition rejected: s' = s, which satisfies all oaths by invariant
    obtain ⟨hs', _⟩ := hActual
    rw [← hs']
    exact hInv o hMem
  case isFalse hNoViolate =>
    -- Transition accepted: proposed state violates no oath
    obtain ⟨hs', _⟩ := hActual
    rw [← hs']
    -- Use helper lemma: ¬any → ∀ ¬
    simp [Bool.not_eq_true] at hNoViolate
    have hNotViolated := not_any_implies_forall_not _ _ o hNoViolate hMem
    simp at hNotViolated
    exact hNotViolated

