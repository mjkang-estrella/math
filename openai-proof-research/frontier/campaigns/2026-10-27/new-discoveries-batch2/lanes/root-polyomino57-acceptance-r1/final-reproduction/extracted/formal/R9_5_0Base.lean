import R9_5_0BaseB0
import R9_5_0BaseB1
import R9_5_0BaseB2
import R9_5_0BaseB3
import R9_5_0BaseB4
import R9_5_0BaseB5
import R9_5_0BaseB6
import R9_5_0BaseB7
import R9_5_0BaseB8
import R9_5_0BaseB9
import R9_5_0BaseB10
import R9_5_0BaseB11
import R9_5_0BaseB12
import R9_5_0BaseB13
import R9_5_0BaseB14
import R9_5_0BaseB15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem base_check : ∀ m : Fin 1024, m.val ≠ 0 → ∀ v : Fin 30,
  (∀ i ∈ decode 10 m.val, point v ∈ group i) → digit (table m.val) v.val ≤ 1 := by
  intro m
  by_cases h8 : m.val < 512
  ·
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
  ·
    by_cases h12 : m.val < 768
    ·
      by_cases h10 : m.val < 640
      ·
        by_cases h9 : m.val < 576
        ·
          have hb : m.val-512 < 64 := by omega
          have he : m.val-512+512 = m.val := by omega
          have hp := base_checkB8 ⟨m.val-512,hb⟩
          simpa only [he] using hp
        ·
          have hb : m.val-576 < 64 := by omega
          have he : m.val-576+576 = m.val := by omega
          have hp := base_checkB9 ⟨m.val-576,hb⟩
          simpa only [he] using hp
      ·
        by_cases h11 : m.val < 704
        ·
          have hb : m.val-640 < 64 := by omega
          have he : m.val-640+640 = m.val := by omega
          have hp := base_checkB10 ⟨m.val-640,hb⟩
          simpa only [he] using hp
        ·
          have hb : m.val-704 < 64 := by omega
          have he : m.val-704+704 = m.val := by omega
          have hp := base_checkB11 ⟨m.val-704,hb⟩
          simpa only [he] using hp
    ·
      by_cases h14 : m.val < 896
      ·
        by_cases h13 : m.val < 832
        ·
          have hb : m.val-768 < 64 := by omega
          have he : m.val-768+768 = m.val := by omega
          have hp := base_checkB12 ⟨m.val-768,hb⟩
          simpa only [he] using hp
        ·
          have hb : m.val-832 < 64 := by omega
          have he : m.val-832+832 = m.val := by omega
          have hp := base_checkB13 ⟨m.val-832,hb⟩
          simpa only [he] using hp
      ·
        by_cases h15 : m.val < 960
        ·
          have hb : m.val-896 < 64 := by omega
          have he : m.val-896+896 = m.val := by omega
          have hp := base_checkB14 ⟨m.val-896,hb⟩
          simpa only [he] using hp
        ·
          have hb : m.val-960 < 64 := by omega
          have he : m.val-960+960 = m.val := by omega
          have hp := base_checkB15 ⟨m.val-960,hb⟩
          simpa only [he] using hp
end R9_5_0
