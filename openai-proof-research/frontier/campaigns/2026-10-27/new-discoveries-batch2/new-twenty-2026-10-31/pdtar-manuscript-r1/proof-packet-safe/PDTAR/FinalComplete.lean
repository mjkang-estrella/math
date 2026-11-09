import PDTAR.SmallStarComplete
import PDTAR.SmallK33Complete
namespace PDTAR

theorem mathdb_353203 (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    TARUnique (completeBipartiteGraph (Fin s) (Fin t)) ↔ (s ≠ 2 ∧ t ≠ 2) :=
  mathdb_353203_conditional starRigidityRemaining threeThreeRigidityRemaining s t hs ht

#print axioms mathdb_353203
end PDTAR
