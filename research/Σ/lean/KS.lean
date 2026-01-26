import Mathlib.Tactic

/-- Peres-Mermin Square: 9 observables, 6 parity constraints (3 rows, 3 cols). -/
abbrev G := Fin 9
def C : List (List G × Bool) := [([0,1,2],false),([3,4,5],false),([6,7,8],false),([0,3,6],false),([1,4,7],false),([2,5,8],true)]
def chk (m : Nat) : Bool := C.all fun (i,p) => i.foldl (fun a x => xor a ((m >>> x.val) % 2 == 1)) false == p

/-- Kochen-Specker Theorem: No global deterministic valuation exists. -/
theorem ks : (List.range 512).all (fun m => !chk m) = true := by native_decide
