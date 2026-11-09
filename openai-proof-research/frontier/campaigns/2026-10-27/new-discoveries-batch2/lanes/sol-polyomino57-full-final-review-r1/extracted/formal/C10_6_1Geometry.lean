import C10_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C10_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem domain_eq : domain 10 6 1 = (Finset.univ : Finset (Fin 38)).image point := by decide
 theorem point_injective : Function.Injective point := by
  have h : ∀ i j : Fin 38, point i = point j → i = j := by decide
  exact h
 theorem groups_mem : ∀ i ∈ Finset.range 6, group i ∈ groups 10 6 1 := by decide
end C10_6_1
