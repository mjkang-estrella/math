import SmallData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Polyomino57.Diagonal.FiniteProof.Small
open Polyomino57
theorem domain_eq : domain 10 10 1 = (Finset.univ : Finset (Fin 60)).image point := by decide
theorem point_injective : Function.Injective point := by
  intro i j
  have h : ∀ i j : Fin 60, point i = point j → i = j := by decide
  exact h i j
theorem groups_mem : ∀ i ∈ (Finset.univ : Finset (Fin 4)), group i ∈ groups 10 10 1 := by decide
end Polyomino57.Diagonal.FiniteProof.Small
