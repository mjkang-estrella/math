import PDTAR.ReductionProof
open PDTAR Finset
open scoped symmDiff
example : (∅ : Finset (Fin 2)) ∆ {(0 : Fin 2)} = ∅ := by
  simp
