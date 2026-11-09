import R9_5_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_checkB3 : ∀ m : Fin 64, (m.val+192) ≠ 0 → ∀ v : Fin 30,
  (∀ i ∈ decode 10 (m.val+192), point v ∈ group i) → digit (table (m.val+192)) v.val ≤ 1 := by decide
end R9_5_0
