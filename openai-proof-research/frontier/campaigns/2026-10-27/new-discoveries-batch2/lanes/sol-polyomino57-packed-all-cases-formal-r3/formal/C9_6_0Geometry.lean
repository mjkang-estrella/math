import C9_6_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C9_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem domain_eq : domain 9 6 0 = (Finset.univ : Finset (Fin 35)).image point := by decide
 theorem point_injective : Function.Injective point := by
  have h : ∀ i j : Fin 35, point i = point j → i = j := by decide
  exact h
 theorem groups_mem : ∀ i ∈ Finset.range 9, group i ∈ groups 9 6 0 := by decide
end C9_6_0
