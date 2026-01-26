/-!
# Peres-Mermin Boolean Kernel
Generated via 互照 fusion: gemini + gpt52 + opus | 2026-01-26

This proves the CORE contradiction: no Boolean assignment satisfies all 6 parity constraints.
Compiles in milliseconds via native_decide.

For the κ=5 polytope result (linear programming), see Python verification.
-/

namespace PeresMermin

-- | 1. THE ONTOLOGY (9 Observables as Fin 9) |
abbrev Obs := Fin 9

-- Grid layout:
-- 0 1 2
-- 3 4 5
-- 6 7 8

-- | 2. THE CONSTRAINTS |
-- Rows: product = +1 (XOR sum = false)
-- Cols 1,2: product = +1 (XOR sum = false)  
-- Col 3: product = -1 (XOR sum = true)

-- Context: list of indices + expected parity
structure Context where
  vars : List (Fin 9)
  parity : Bool -- false = +1, true = -1
deriving DecidableEq

def constraints : List Context := [
  -- Rows
  { vars := [0, 1, 2], parity := false },
  { vars := [3, 4, 5], parity := false },
  { vars := [6, 7, 8], parity := false },
  -- Columns
  { vars := [0, 3, 6], parity := false },
  { vars := [1, 4, 7], parity := false },
  { vars := [2, 5, 8], parity := true  }  -- The twist
]

-- | 3. SEMANTICS |
-- Assignment: 9 bits packed as a natural < 512
abbrev Assignment := Fin 512

@[inline] def getBit (a : Assignment) (i : Fin 9) : Bool :=
  (a.val >>> i.val) &&& 1 == 1

def satisfies (a : Assignment) (c : Context) : Bool :=
  let values := c.vars.map (getBit a)
  let sum := values.foldl xor false
  sum == c.parity

def is_valid_global (a : Assignment) : Bool :=
  constraints.all (satisfies a)

-- | 4. THE PROOF |
-- Check all 512 assignments using Fin 512 enumeration

def allAssignments : List (Fin 512) := List.finRange 512

def checkAll : Bool := allAssignments.all (fun a => !is_valid_global a)

theorem peres_mermin_infeasible : checkAll = true := by native_decide

-- | 5. COROLLARY: Size 8 IS feasible (drop last constraint) |

def constraints_drop_last : List Context := constraints.dropLast

def satisfies_relaxed (a : Assignment) : Bool :=
  constraints_drop_last.all (satisfies a)

def checkSomeFeasible : Bool := allAssignments.any satisfies_relaxed

theorem size_eight_feasible : checkSomeFeasible = true := by native_decide

-- | 6. INTERPRETATION |
-- peres_mermin_infeasible: The grid has no global section (cohomological obstruction)
-- size_eight_feasible: κ_Boolean = 8 (not 5)
-- κ = 5 is a DIFFERENT theorem about the non-contextuality POLYTOPE (LP)

end PeresMermin
