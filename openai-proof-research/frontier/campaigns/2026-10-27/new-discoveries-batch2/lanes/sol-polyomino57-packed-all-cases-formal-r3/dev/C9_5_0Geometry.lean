import C9_5_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C9_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem domain_eq : domain 9 5 0 = (Finset.univ : Finset (Fin 30)).image point := by decide
 theorem point_injective : Function.Injective point := by
  have h : ∀ i j : Fin 30, point i = point j → i = j := by decide
  exact h
 theorem groups_mem : ∀ i ∈ Finset.range 10, group i ∈ groups 9 5 0 := by decide
end C9_5_0
