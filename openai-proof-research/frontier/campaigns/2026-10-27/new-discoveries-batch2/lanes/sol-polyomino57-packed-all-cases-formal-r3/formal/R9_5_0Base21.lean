import R9_5_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check21 : ∀ m : Fin 16, (m.val+336) ≠ 0 → ∀ v : Fin 30,
  (∀ i ∈ decode 10 (m.val+336), point v ∈ group i) → digit (table (m.val+336)) v.val ≤ 1 := by decide
end R9_5_0
