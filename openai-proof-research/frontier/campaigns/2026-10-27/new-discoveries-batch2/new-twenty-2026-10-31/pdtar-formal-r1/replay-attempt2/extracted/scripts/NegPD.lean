import PDTAR.Fidelity
example : PDTAR.IsPD (completeBipartiteGraph (Fin 2) (Fin 3)) ∅ := by
  exact PDTAR.isPD_univ _
