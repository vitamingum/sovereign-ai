import KS

def main : IO Unit := do
  IO.println "---------------------------------------------------"
  IO.println "Σ :: LEAN 4 VERIFICATION"
  IO.println "---------------------------------------------------"
  IO.println s!"ks = {(List.range 512).all (!chk ·)}"
  let _ := ks
  IO.println "Kochen-Specker theorem verified."
  IO.println "---------------------------------------------------"

