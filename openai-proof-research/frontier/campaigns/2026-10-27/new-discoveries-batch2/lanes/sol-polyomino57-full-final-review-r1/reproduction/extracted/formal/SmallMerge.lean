import SmallData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Polyomino57.Diagonal.FiniteProof.Small
open Polyomino57
theorem merge_check : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, ∀ B ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → B.Nonempty → Disjoint A B → ∀ z : Fin 60, z ∈ Finset.univ →
 value (A ∪ B) z + 1 ≤ value A z + value B z := by decide
end Polyomino57.Diagonal.FiniteProof.Small
