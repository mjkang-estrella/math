import PDTAR.Final
open PDTAR
example : TARUnique (completeBipartiteGraph (Fin 2) (Fin 3)) := by
  have hn := two_of_witness twoWitnessRemaining 2 3 (by omega) (by omega) (Or.inl rfl)
  simp_all
