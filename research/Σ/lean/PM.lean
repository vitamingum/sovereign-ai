/-!
# Peres-Mermin Polytope Constraints
Generated via 互照 fusion: gemini + gpt52 + opus | 2026-01-26

Encodes the NC polytope constraints for Peres-Mermin:
- 24 variables: 6 contexts × 4 sections each
- Normalization: Σ p_i = 1 per context
- Marginal consistency: overlapping observables must agree
- Determinism: when observable values are fixed
-/

import FarkasKernel

namespace PM

-- | STRUCTURE |
-- 9 observables arranged in 3×3 grid
-- 6 contexts (3 rows + 3 columns)
-- Each context has 4 sections (local assignments satisfying parity)

-- Context indices
abbrev Context := Fin 6

-- Section indices within a context
abbrev Section := Fin 4

-- Variable index: context × section
abbrev Var := Fin 24

def toVar (c : Context) (s : Section) : Var := ⟨c.val * 4 + s.val, by omega⟩

-- | PERES-MERMIN GRID |
-- Contexts:
--   0: row 0 (obs 0,1,2)
--   1: row 1 (obs 3,4,5)
--   2: row 2 (obs 6,7,8)
--   3: col 0 (obs 0,3,6)
--   4: col 1 (obs 1,4,7)
--   5: col 2 (obs 2,5,8)

-- Observable indices per context
def contextObs : Context → List (Fin 9)
  | ⟨0, _⟩ => [0, 1, 2]
  | ⟨1, _⟩ => [3, 4, 5]
  | ⟨2, _⟩ => [6, 7, 8]
  | ⟨3, _⟩ => [0, 3, 6]
  | ⟨4, _⟩ => [1, 4, 7]
  | ⟨5, _⟩ => [2, 5, 8]

-- Parity for each context (+1 or -1 product)
-- Rows: +1, Columns 0,1: +1, Column 2: -1
def contextParity : Context → Int
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => -1

-- Sections: 4 local assignments satisfying parity
-- For parity +1: (-1,-1,-1), (-1,1,1), (1,-1,1), (1,1,-1)
-- For parity -1: (-1,-1,1), (-1,1,-1), (1,-1,-1), (1,1,1)
def sectionValues (parity : Int) (s : Section) : Fin 3 → Int :=
  if parity == 1 then
    match s.val with
    | 0 => fun i => [-1, -1, -1].get! i.val
    | 1 => fun i => [-1, 1, 1].get! i.val
    | 2 => fun i => [1, -1, 1].get! i.val
    | _ => fun i => [1, 1, -1].get! i.val
  else
    match s.val with
    | 0 => fun i => [-1, -1, 1].get! i.val
    | 1 => fun i => [-1, 1, -1].get! i.val
    | 2 => fun i => [1, -1, -1].get! i.val
    | _ => fun i => [1, 1, 1].get! i.val

-- | CONSTRAINT BUILDING |
-- These will be used by the Python script to build A, b

-- Normalization constraints: for each context, Σ_s p[c,s] = 1
-- 6 equality constraints

-- Marginal consistency: for overlapping observables across contexts
-- E.g., obs 0 appears in context 0 (row 0) and context 3 (col 0)
-- The marginal probability of obs 0 = +1 must match

-- Determinism: when we fix observable values, some sections become impossible

end PM
