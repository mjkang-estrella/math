import R8_8_0BaseB0
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_8_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check : ∀ m : Fin 64, m.val ≠ 0 → ∀ v : Fin 41,
  (∀ i ∈ decode 6 m.val, point v ∈ group i) → digit (table m.val) v.val ≤ 1 := by
  intro m
  have hb : m.val-0 < 64 := by omega
  have he : m.val-0+0 = m.val := by omega
  have hp := base_checkB0 ⟨m.val-0,hb⟩
  simpa only [he] using hp
end R8_8_0
