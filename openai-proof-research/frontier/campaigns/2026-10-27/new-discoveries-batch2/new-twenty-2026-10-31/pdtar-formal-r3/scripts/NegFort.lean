import PDTAR.Final
open PDTAR
example : IsFort (completeBipartiteGraph (Fin 2) (Fin 3)) ∅ := by
  simp [IsFort]
