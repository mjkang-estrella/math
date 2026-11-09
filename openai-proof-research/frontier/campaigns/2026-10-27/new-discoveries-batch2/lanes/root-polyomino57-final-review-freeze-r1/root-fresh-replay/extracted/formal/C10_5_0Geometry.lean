import C10_5_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C10_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem domain_eq : domain 10 5 0 = (Finset.univ : Finset (Fin 33)).image point := by decide
 theorem point_injective : Function.Injective point := by
  have h : ∀ i j : Fin 33, point i = point j → i = j := by decide
  exact h
 theorem groups_mem : ∀ i ∈ Finset.range 7, group i ∈ groups 10 5 0 := by decide
end C10_5_0
