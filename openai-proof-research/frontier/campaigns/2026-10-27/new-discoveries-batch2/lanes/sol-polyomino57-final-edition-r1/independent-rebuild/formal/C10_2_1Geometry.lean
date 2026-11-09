import C10_2_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C10_2_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem domain_eq : domain 10 2 1 = (Finset.univ : Finset (Fin 16)).image point := by decide
 theorem point_injective : Function.Injective point := by
  have h : ∀ i j : Fin 16, point i = point j → i = j := by decide
  exact h
 theorem groups_mem : ∀ i ∈ Finset.range 6, group i ∈ groups 10 2 1 := by decide
end C10_2_1
