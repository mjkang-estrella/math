import C8_8_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C8_8_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check : ∀ m : Fin 256, m.val ≠ 0 → ∀ v : Fin 40,
  (∀ i ∈ decode 8 m.val, point v ∈ group i) → digit (table m.val) v.val ≤ 1 := by decide
end C8_8_1
