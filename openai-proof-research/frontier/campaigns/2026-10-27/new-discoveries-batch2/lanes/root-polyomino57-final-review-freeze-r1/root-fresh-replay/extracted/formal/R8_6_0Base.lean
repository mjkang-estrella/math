import R8_6_0BaseB0
import R8_6_0BaseB1
import R8_6_0BaseB2
import R8_6_0BaseB3
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check : ∀ m : Fin 256, m.val ≠ 0 → ∀ v : Fin 32,
  (∀ i ∈ decode 8 m.val, point v ∈ group i) → digit (table m.val) v.val ≤ 1 := by
  intro m
  by_cases h2 : m.val < 128
  ·
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
  ·
    by_cases h3 : m.val < 192
    ·
      have hb : m.val-128 < 64 := by omega
      have he : m.val-128+128 = m.val := by omega
      have hp := base_checkB2 ⟨m.val-128,hb⟩
      simpa only [he] using hp
    ·
      have hb : m.val-192 < 64 := by omega
      have he : m.val-192+192 = m.val := by omega
      have hp := base_checkB3 ⟨m.val-192,hb⟩
      simpa only [he] using hp
end R8_6_0
