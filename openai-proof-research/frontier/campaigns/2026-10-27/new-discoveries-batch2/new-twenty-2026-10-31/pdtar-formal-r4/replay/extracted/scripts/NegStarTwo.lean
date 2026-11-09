import PDTAR.FinalComplete
open PDTAR
example : TARUnique (completeBipartiteGraph (Fin 1) (Fin 2)) := by
  have hn := two_of_witness twoWitnessRemaining 1 2 (by omega) (by omega) (Or.inr rfl)
  simp_all
