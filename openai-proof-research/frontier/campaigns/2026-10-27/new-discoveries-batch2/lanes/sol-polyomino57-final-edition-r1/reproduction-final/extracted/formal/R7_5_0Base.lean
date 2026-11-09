import R7_5_0BaseB0
import R7_5_0BaseB1
import R7_5_0BaseB2
import R7_5_0BaseB3
import R7_5_0BaseB4
import R7_5_0BaseB5
import R7_5_0BaseB6
import R7_5_0BaseB7
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check : ∀ m : Fin 512, m.val ≠ 0 → ∀ v : Fin 24,
  (∀ i ∈ decode 9 m.val, point v ∈ group i) → digit (table m.val) v.val ≤ 1 := by
  intro m
  by_cases h4 : m.val < 256
  ·
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
  ·
    by_cases h6 : m.val < 384
    ·
      by_cases h5 : m.val < 320
      ·
        have hb : m.val-256 < 64 := by omega
        have he : m.val-256+256 = m.val := by omega
        have hp := base_checkB4 ⟨m.val-256,hb⟩
        simpa only [he] using hp
      ·
        have hb : m.val-320 < 64 := by omega
        have he : m.val-320+320 = m.val := by omega
        have hp := base_checkB5 ⟨m.val-320,hb⟩
        simpa only [he] using hp
    ·
      by_cases h7 : m.val < 448
      ·
        have hb : m.val-384 < 64 := by omega
        have he : m.val-384+384 = m.val := by omega
        have hp := base_checkB6 ⟨m.val-384,hb⟩
        simpa only [he] using hp
      ·
        have hb : m.val-448 < 64 := by omega
        have he : m.val-448+448 = m.val := by omega
        have hp := base_checkB7 ⟨m.val-448,hb⟩
        simpa only [he] using hp
end R7_5_0
