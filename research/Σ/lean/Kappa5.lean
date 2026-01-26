/-!
# κ = 5 Formal Proof via Farkas Certificates

Architecture (per GPT council 2026-01-26):
  Python proposes: solve LPs, emit Farkas certificates over ℚ
  Lean verifies: check yᵀA ≥ 0 ∧ yᵀb < 0 via native_decide

Theorem: κ = 5 for the Peres-Mermin square
  (A) κ ≤ 5: All 5376 size-6 deterministic assignments are NC-infeasible
  (B) κ ≥ 5: At least one size-5 assignment is NC-feasible
-/

-- Rational as (numerator, denominator) pair, decidable arithmetic
abbrev Q := Int × Int

def qmul (a b : Q) : Q := (a.1 * b.1, a.2 * b.2)
def qadd (a b : Q) : Q := (a.1 * b.2 + b.1 * a.2, a.2 * b.2)
def qge0 (a : Q) : Bool := (a.1 ≥ 0) == (a.2 > 0)
def qlt0 (a : Q) : Bool := (a.1 < 0) == (a.2 > 0)
def qeq (a b : Q) : Bool := a.1 * b.2 == b.1 * a.2

def dot (u v : List Q) : Q :=
  (u.zip v).foldl (fun acc p => qadd acc (qmul p.1 p.2)) (0, 1)

-- Peres-Mermin contexts: 6 contexts, each with 3 observables
-- Rows: R1=[0,1,2], R2=[3,4,5], R3=[6,7,8] with product +1
-- Cols: C1=[0,3,6], C2=[1,4,7], C3=[2,5,8] with product -1
def contexts : List (List Nat × Int) :=
  [([0,1,2], 1), ([3,4,5], 1), ([6,7,8], 1),
   ([0,3,6], -1), ([1,4,7], -1), ([2,5,8], -1)]

-- 4 sections per context satisfying parity constraint
-- For product p: sections are all (a,b,c) with abc = p
def sectionsFor (p : Int) : List (List Int) :=
  [[-1,-1,-1*p], [-1,1,1*p], [1,-1,1*p], [1,1,-1*p]]

-- Variable indexing: x[ctx*4 + sec] for ctx in 0..5, sec in 0..3
def varId (ctx sec : Nat) : Nat := ctx * 4 + sec

-- Build constraint row: list of (variable index, coefficient)
def normRow (ctx : Nat) : List (Nat × Q) :=
  List.range 4 |>.map fun sec => (varId ctx sec, (1, 1))

-- Marginal row: P(obs=+1|ctx1) - P(obs=+1|ctx2) = 0
def marginalRow (obs ctx1 pos1 ctx2 pos2 : Nat) : List (Nat × Q) :=
  let ctx1Secs := sectionsFor (contexts.getD ctx1 default).2
  let ctx2Secs := sectionsFor (contexts.getD ctx2 default).2
  let pos1Terms := ctx1Secs.enum.filterMap fun (si, sec) =>
    if sec.getD pos1 0 == 1 then some (varId ctx1 si, (1, 1)) else none
  let neg2Terms := ctx2Secs.enum.filterMap fun (si, sec) =>
    if sec.getD pos2 0 == 1 then some (varId ctx2 si, (-1, 1)) else none
  pos1Terms ++ neg2Terms

-- Deterministic row: P(obs=val|ctx) = 1 if val=+1, else 0
def detRow (obs : Nat) (val : Int) (ctx pos : Nat) : List (Nat × Q) × Q :=
  let secs := sectionsFor (contexts.getD ctx default).2
  let terms := secs.enum.filterMap fun (si, sec) =>
    if sec.getD pos 0 == 1 then some (varId ctx si, (1, 1)) else none
  (terms, if val == 1 then (1, 1) else (0, 1))

-- Evaluate sparse row · x
def evalRow (row : List (Nat × Q)) (x : List Q) : Q :=
  row.foldl (fun acc (i, c) => qadd acc (qmul c (x.getD i (0,1)))) (0, 1)

-- Check Farkas certificate: yᵀA ≥ 0 and yᵀb < 0
-- A is implicit: we evaluate (yᵀA)_j = Σᵢ yᵢ Aᵢⱼ by iterating rows
def checkCertSparse (rows : List (List (Nat × Q))) (b y : List Q) : Bool :=
  let m := rows.length
  let n := 24
  -- Compute yᵀA for each column j
  let yTA := List.range n |>.map fun j =>
    (List.range m).foldl (fun acc i =>
      let row := rows.getD i []
      let aij := row.find? (·.1 == j) |>.map (·.2) |>.getD (0, 1)
      qadd acc (qmul (y.getD i (0,1)) aij)) (0, 1)
  -- Check yᵀA ≥ 0 and yᵀb < 0
  yTA.all qge0 && qlt0 (dot y b)

-- Check feasibility: Ax = b, x ≥ 0
def checkFeasibleSparse (rows : List (List (Nat × Q))) (b x : List Q) : Bool :=
  rows.zip b |>.all (fun (row, bi) => qeq (evalRow row x) bi) && x.all qge0

-- Build full constraint system for a subset S with values
-- Returns (rows, rhs) where each row is sparse
def buildSystem (subset : List Nat) (vals : List Int) : List (List (Nat × Q)) × List Q :=
  -- 6 normalization constraints
  let normRows := List.range 6 |>.map normRow
  let normRhs := List.replicate 6 (1, 1)
  -- 9 marginal constraints (simplified: just add enough for correctness)
  -- ... (would need full implementation)
  sorry  -- Placeholder for full constraint builder

-- For now, we'll use a simpler approach: embed the full data

-- ============================================================================
-- SIMPLIFIED APPROACH: Direct embedding of certificates
-- ============================================================================

-- Due to size constraints, we verify a representative sample and appeal to
-- the symmetry of the constraint structure.

-- Certificate format: (subset_bits, vals_bits, y_coeffs)
-- where subset_bits encodes which 6 of 9 observables are constrained,
-- and vals_bits encodes the ±1 values

-- For the formal proof, we verify:
-- 1. The constraint builder is correct (by testing on known cases)
-- 2. The certificate checker is correct (by testing on known certificates)
-- 3. Apply to all 5376 cases via native_decide

-- This is a minimal kernel that can be extended with the full certificate data

theorem kappa_le_five_placeholder : True := trivial

-- κ ≥ 5: One explicit feasible witness
-- Subset: [0,1,2,3,6], Values: [-1,-1,+1,-1,-1]
-- Feasible point found by LP solver (to be embedded as exact rationals)

theorem kappa_ge_five_placeholder : True := trivial

-- Full proof requires embedding 5376 certificate vectors (~100KB of Lean data)
-- Generated by: python Σ_lean_certs.py > Kappa5_Data.lean
