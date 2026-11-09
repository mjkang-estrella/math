import R7_6_0EdgeB0
import R7_6_0EdgeB1
import R7_6_0EdgeB2
import R7_6_0EdgeB3
import R7_6_0EdgeB4
import R7_6_0EdgeB5
import R7_6_0EdgeB6
import R7_6_0EdgeB7
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem edge_check : ∀ m : Fin 256, m.val ≠ 0 → ∀ vw ∈ edges,
  digit (table m.val) vw.1.val ≤ digit (table m.val) vw.2.val + 1 := by
  intro m
  by_cases h4 : m.val < 128
  ·
    by_cases h2 : m.val < 64
    ·
      by_cases h1 : m.val < 32
      ·
        have hb : m.val-0 < 32 := by omega
        have he : m.val-0+0 = m.val := by omega
        have hp := edge_checkB0 ⟨m.val-0,hb⟩
        simpa only [he] using hp
      ·
        have hb : m.val-32 < 32 := by omega
        have he : m.val-32+32 = m.val := by omega
        have hp := edge_checkB1 ⟨m.val-32,hb⟩
        simpa only [he] using hp
    ·
      by_cases h3 : m.val < 96
      ·
        have hb : m.val-64 < 32 := by omega
        have he : m.val-64+64 = m.val := by omega
        have hp := edge_checkB2 ⟨m.val-64,hb⟩
        simpa only [he] using hp
      ·
        have hb : m.val-96 < 32 := by omega
        have he : m.val-96+96 = m.val := by omega
        have hp := edge_checkB3 ⟨m.val-96,hb⟩
        simpa only [he] using hp
  ·
    by_cases h6 : m.val < 192
    ·
      by_cases h5 : m.val < 160
      ·
        have hb : m.val-128 < 32 := by omega
        have he : m.val-128+128 = m.val := by omega
        have hp := edge_checkB4 ⟨m.val-128,hb⟩
        simpa only [he] using hp
      ·
        have hb : m.val-160 < 32 := by omega
        have he : m.val-160+160 = m.val := by omega
        have hp := edge_checkB5 ⟨m.val-160,hb⟩
        simpa only [he] using hp
    ·
      by_cases h7 : m.val < 224
      ·
        have hb : m.val-192 < 32 := by omega
        have he : m.val-192+192 = m.val := by omega
        have hp := edge_checkB6 ⟨m.val-192,hb⟩
        simpa only [he] using hp
      ·
        have hb : m.val-224 < 32 := by omega
        have he : m.val-224+224 = m.val := by omega
        have hp := edge_checkB7 ⟨m.val-224,hb⟩
        simpa only [he] using hp
end R7_6_0
