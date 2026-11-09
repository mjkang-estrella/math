import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem domain_eq : domain 6 6 1 = (Finset.univ : Finset (Fin 24)).image point := by decide
 theorem point_injective : Function.Injective point := by
  have h : ∀ i j : Fin 24, point i = point j → i = j := by decide
  exact h
 theorem groups_mem : ∀ i ∈ Finset.range 12, group i ∈ groups 6 6 1 := by decide
end R6_6_1
