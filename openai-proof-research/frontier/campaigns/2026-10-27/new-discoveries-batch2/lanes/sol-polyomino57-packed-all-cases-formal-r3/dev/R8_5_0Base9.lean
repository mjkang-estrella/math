import R8_5_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check9 : ∀ m : Fin 16, (m.val+144) ≠ 0 → ∀ v : Fin 27,
  (∀ i ∈ decode 9 (m.val+144), point v ∈ group i) → digit (table (m.val+144)) v.val ≤ 1 := by decide
end R8_5_0
