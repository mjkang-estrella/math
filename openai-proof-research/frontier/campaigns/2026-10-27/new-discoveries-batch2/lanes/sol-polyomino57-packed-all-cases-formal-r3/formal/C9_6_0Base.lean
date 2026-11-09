import C9_6_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C9_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check : ∀ m : Fin 512, m.val ≠ 0 → ∀ v : Fin 35,
  (∀ i ∈ decode 9 m.val, point v ∈ group i) → digit (table m.val) v.val ≤ 1 := by decide
end C9_6_0
