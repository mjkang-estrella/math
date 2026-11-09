import R9_6_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check24 : ∀ m : Fin 16, (m.val+384) ≠ 0 → ∀ v : Fin 35,
  (∀ i ∈ decode 9 (m.val+384), point v ∈ group i) → digit (table (m.val+384)) v.val ≤ 1 := by decide
end R9_6_0
