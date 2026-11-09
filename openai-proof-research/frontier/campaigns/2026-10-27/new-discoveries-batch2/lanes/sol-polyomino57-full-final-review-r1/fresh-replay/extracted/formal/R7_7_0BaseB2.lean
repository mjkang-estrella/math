import R7_7_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7_7_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_checkB2 : ∀ m : Fin 64, (m.val+128) ≠ 0 → ∀ v : Fin 32,
  (∀ i ∈ decode 8 (m.val+128), point v ∈ group i) → digit (table (m.val+128)) v.val ≤ 1 := by decide
end R7_7_0
