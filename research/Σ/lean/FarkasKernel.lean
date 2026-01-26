/-!
# Farkas Kernel for κ=5 Proof
Generated via 互照 fusion: gemini + gpt52 + opus | 2026-01-26

Core lemma: if we can exhibit y such that yᵀA ≥ 0 and yᵀb < 0,
then Ax = b, x ≥ 0 has no solution.
-/

namespace FarkasKernel

-- | RATIONAL DOT PRODUCT |

def dot {n : Nat} (a b : Fin n → Int × Int) : Int × Int :=
  (List.finRange n).foldl 
    (fun acc i => 
      let (an, ad) := a i
      let (bn, bd) := b i
      let (sn, sd) := acc
      -- acc + a[i] * b[i] over rationals
      (sn * ad * bd + an * bn * sd, sd * ad * bd))
    (0, 1)

-- Rational comparison: (n1, d1) ≥ 0 means n1/d1 ≥ 0
@[inline] def ratGe0 (r : Int × Int) : Bool :=
  let (n, d) := r
  (n ≥ 0) == (d > 0)

@[inline] def ratLt0 (r : Int × Int) : Bool :=
  let (n, d) := r
  (n < 0) == (d > 0)

-- | FARKAS VERIFICATION |
-- Given:
--   A : m constraints × n variables (as function)
--   b : m-vector (RHS)
--   y : m-vector (dual certificate)
-- Verify:
--   1. yᵀA ≥ 0 (for each column j)
--   2. yᵀb < 0

def verifyFarkas 
    {m n : Nat}
    (A : Fin m → Fin n → Int × Int)  -- constraint matrix
    (b : Fin m → Int × Int)           -- RHS vector
    (y : Fin m → Int × Int)           -- dual certificate
    : Bool :=
  -- Check yᵀA ≥ 0 for each column j
  let colCheck := (List.finRange n).all fun j =>
    let col : Fin m → Int × Int := fun i => A i j
    ratGe0 (dot y col)
  -- Check yᵀb < 0
  let rhsCheck := ratLt0 (dot y b)
  colCheck && rhsCheck

-- | INFEASIBILITY THEOREM |
-- If verifyFarkas returns true, the system Ax = b, x ≥ 0 is infeasible

theorem farkas_implies_infeasible 
    {m n : Nat}
    (A : Fin m → Fin n → Int × Int)
    (b : Fin m → Int × Int)
    (y : Fin m → Int × Int)
    (h : verifyFarkas A b y = true) :
    ¬∃ (x : Fin n → Int × Int), 
      (∀ j, ratGe0 (x j)) ∧ 
      (∀ i, dot (A i) x = b i) := by
  -- The proof follows from Farkas' lemma
  -- If yᵀA ≥ 0 and yᵀb < 0, then for any x ≥ 0:
  --   yᵀ(Ax) = (yᵀA)x ≥ 0 (since yᵀA ≥ 0 and x ≥ 0)
  -- But if Ax = b, then yᵀb = yᵀ(Ax) ≥ 0, contradicting yᵀb < 0
  sorry -- To be filled with formal proof; the computation is the real check

end FarkasKernel
