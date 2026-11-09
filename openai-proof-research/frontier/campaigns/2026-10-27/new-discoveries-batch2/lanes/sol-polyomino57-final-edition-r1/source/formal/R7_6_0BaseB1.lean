import R7_6_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_checkB1 : ∀ m : Fin 64, (m.val+64) ≠ 0 → ∀ v : Fin 28,
  (∀ i ∈ decode 8 (m.val+64), point v ∈ group i) → digit (table (m.val+64)) v.val ≤ 1 := by decide
end R7_6_0
