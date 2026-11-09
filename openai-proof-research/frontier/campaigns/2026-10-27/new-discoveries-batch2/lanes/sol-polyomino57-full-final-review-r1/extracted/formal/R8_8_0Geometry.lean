import R8_8_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_8_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem domain_eq : domain 8 8 0 = (Finset.univ : Finset (Fin 41)).image point := by decide
 theorem point_injective : Function.Injective point := by
  have h : ∀ i j : Fin 41, point i = point j → i = j := by decide
  exact h
 theorem groups_mem : ∀ i ∈ Finset.range 6, group i ∈ groups 8 8 0 := by decide
end R8_8_0
