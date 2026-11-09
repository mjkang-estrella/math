import R8_7_0BaseB0
import R8_7_0BaseB1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_7_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check : ∀ m : Fin 128, m.val ≠ 0 → ∀ v : Fin 36,
  (∀ i ∈ decode 7 m.val, point v ∈ group i) → digit (table m.val) v.val ≤ 1 := by
  intro m
  by_cases h1 : m.val < 64
  ·
    have hb : m.val-0 < 64 := by omega
    have he : m.val-0+0 = m.val := by omega
    have hp := base_checkB0 ⟨m.val-0,hb⟩
    simpa only [he] using hp
  ·
    have hb : m.val-64 < 64 := by omega
    have he : m.val-64+64 = m.val := by omega
    have hp := base_checkB1 ⟨m.val-64,hb⟩
    simpa only [he] using hp
end R8_7_0
