import R9_3_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_3_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_checkB0 : ∀ m : Fin 64, (m.val+0) ≠ 0 → ∀ v : Fin 20,
  (∀ i ∈ decode 6 (m.val+0), point v ∈ group i) → digit (table (m.val+0)) v.val ≤ 1 := by decide
end R9_3_0
