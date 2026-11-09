import R8_4_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_4_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check10 : ∀ m : Fin 16, (m.val+160) ≠ 0 → ∀ v : Fin 22,
  (∀ i ∈ decode 9 (m.val+160), point v ∈ group i) → digit (table (m.val+160)) v.val ≤ 1 := by decide
end R8_4_1
