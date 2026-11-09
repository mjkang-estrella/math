import C10_6_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C10_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check : ∀ m : Fin 128, m.val ≠ 0 → ∀ v : Fin 39,
  (∀ i ∈ decode 7 m.val, point v ∈ group i) → digit (table m.val) v.val ≤ 1 := by decide
end C10_6_0
