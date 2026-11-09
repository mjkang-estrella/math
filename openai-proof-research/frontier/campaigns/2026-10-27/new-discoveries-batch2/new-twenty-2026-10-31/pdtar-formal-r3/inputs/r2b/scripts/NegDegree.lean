import PDTAR.ReductionProof
open PDTAR Finset
example : Nat.card ((tar (⊥ : SimpleGraph (Fin 2))).neighborSet
    ⟨univ,isPD_univ _⟩) > Fintype.card (Fin 2) := by
  have h := reduction_degree_le (⊥ : SimpleGraph (Fin 2)) ⟨univ,isPD_univ _⟩
  omega
