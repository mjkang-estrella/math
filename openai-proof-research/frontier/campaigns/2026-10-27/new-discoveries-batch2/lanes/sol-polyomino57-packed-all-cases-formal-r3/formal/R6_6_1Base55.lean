import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check55 : ∀ m : Fin 16, (m.val+880) ≠ 0 → ∀ v : Fin 24,
  (∀ i ∈ decode 12 (m.val+880), point v ∈ group i) → digit (table (m.val+880)) v.val ≤ 1 := by decide
end R6_6_1
