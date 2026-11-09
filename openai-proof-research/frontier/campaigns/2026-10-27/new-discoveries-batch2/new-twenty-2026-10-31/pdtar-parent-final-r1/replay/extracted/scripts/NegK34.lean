import PDTAR.Final
open PDTAR
example : ¬ TARUnique (completeBipartiteGraph (Fin 3) (Fin 4)) := by
  have hp := mathdb_353203_core 3 4 (by omega) (by omega) (Or.inr (by omega))
  simp_all
