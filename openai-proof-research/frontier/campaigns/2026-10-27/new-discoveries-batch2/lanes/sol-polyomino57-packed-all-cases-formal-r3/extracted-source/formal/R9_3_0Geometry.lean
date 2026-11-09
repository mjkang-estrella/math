import R9_3_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_3_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem domain_eq : domain 9 3 0 = (Finset.univ : Finset (Fin 20)).image point := by decide
 theorem point_injective : Function.Injective point := by
  have h : ∀ i j : Fin 20, point i = point j → i = j := by decide
  exact h
 theorem groups_mem : ∀ i ∈ Finset.range 6, group i ∈ groups 9 3 0 := by decide
end R9_3_0
