import PDTAR.ReductionProof
import PDTAR.SmallStatement
namespace PDTAR

/-- All positive sizes outside the previously known star and (3,3) cases. -/
theorem mathdb_353203_core (s t : ℕ) (hs : 3 ≤ s) (ht : 3 ≤ t)
    (hne : s ≠ 3 ∨ t ≠ 3) :
    TARUnique (completeBipartiteGraph (Fin s) (Fin t)) := by
  intro W _ _ H hH hiso
  obtain ⟨H',⟨e⟩,he⟩ := reductionRemaining _ _ _ H
    (sum_noIsolated s t (by omega) (by omega)) hH hiso
  have hcore := coreRemaining _ _ H' (leftPart s t) (rightPart s t) (sum_parts s t)
    (by simpa [leftPart] using hs) (by simpa [rightPart] using ht)
    (by simpa [leftPart,rightPart] using hne) he
  subst H'
  exact ⟨e⟩

/-- Partial-round fallback: exactly the two still-open rigidity Props are hypotheses. -/
theorem mathdb_353203_conditional (hS : StarRigidityRemaining)
    (hT : ThreeThreeRigidityRemaining)
    (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    TARUnique (completeBipartiteGraph (Fin s) (Fin t)) ↔ (s ≠ 2 ∧ t ≠ 2) :=
  mathdb_353203_of_reduction_conditional reductionRemaining hS hT twoWitnessRemaining s t hs ht

#print axioms twoWitnessRemaining
#print axioms mathdb_353203_core
#print axioms mathdb_353203_conditional
end PDTAR
