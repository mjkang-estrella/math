import SmallData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Polyomino57.Diagonal.FiniteProof.Small
open Polyomino57
theorem base_check : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ z : Fin 60, z ∈ Finset.univ →
 (∀ i ∈ A, point z ∈ group i) → value A z ≤ 1 := by decide
end Polyomino57.Diagonal.FiniteProof.Small
