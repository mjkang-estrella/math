import PDTAR.CoreProofAssembly
namespace PDTAR
open Finset

theorem coreRemaining : CoreRemaining := core_remaining_proved

/-- CONDITIONAL: the labelled counterexample witness construction remains open. -/
theorem twoRemaining_conditional (hT : TwoWitnessRemaining) : TwoRemaining :=
  two_of_witness hT

theorem edgeRemaining_of_reduction (hR : ReductionRemaining) : EdgeRemaining :=
  small_edge_of_reduction hR

/-- CONDITIONAL: star rigidity remains open. -/
theorem starsRemaining_of_reduction_conditional (hR : ReductionRemaining)
    (hS : StarRigidityRemaining) : StarsRemaining := stars_of_rigidity hR hS

/-- CONDITIONAL: six-vertex rigidity remains open. -/
theorem threeThreeRemaining_of_reduction_conditional (hR : ReductionRemaining)
    (hT : ThreeThreeRigidityRemaining) : ThreeThreeRemaining := threeThree_of_rigidity hR hT

/-- CONDITIONAL fallback: all three residual Props are explicit hypotheses. -/
theorem mathdb_353203_of_reduction_conditional (hR : ReductionRemaining)
    (hS : StarRigidityRemaining) (hT : ThreeThreeRigidityRemaining)
    (hW : TwoWitnessRemaining)
    (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    TARUnique (completeBipartiteGraph (Fin s) (Fin t)) ↔ (s ≠ 2 ∧ t ≠ 2) := by
  have reduction := hR
  have core := coreRemaining
  have edge := edgeRemaining_of_reduction hR
  have stars := starsRemaining_of_reduction_conditional hR hS
  have threeThree := threeThreeRemaining_of_reduction_conditional hR hT
  have two := twoRemaining_conditional hW

  constructor
  · intro hu
    constructor
    · intro he; exact two s t hs ht (.inl he) hu
    · intro he; exact two s t hs ht (.inr he) hu
  · rintro ⟨hs2,ht2⟩
    by_cases hs1 : s = 1
    · subst s
      by_cases ht1 : t = 1
      · subst t; exact edge
      · exact (stars t (by omega)).1
    by_cases ht1 : t = 1
    · subst t; exact (stars s (by omega)).2
    by_cases h33 : s = 3 ∧ t = 3
    · obtain ⟨rfl,rfl⟩ := h33; exact threeThree
    have hs3 : 3 ≤ s := by omega
    have ht3 : 3 ≤ t := by omega
    intro W _ _ H hH hiso
    obtain ⟨H',⟨e⟩,hpd⟩ := reduction _ _ _ H (sum_noIsolated s t hs ht) hH hiso
    have hcore := core _ _ H' (leftPart s t) (rightPart s t) (sum_parts s t)
      (by simpa [leftPart] using hs3) (by simpa [rightPart] using ht3)
      (by simpa [leftPart,rightPart] using (not_and_or.mp h33)) hpd
    subst H'
    exact ⟨e⟩
end PDTAR
