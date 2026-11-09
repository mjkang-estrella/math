import R6_6_1BoundsB0
import R6_6_1BoundsB1
import R6_6_1BoundsB2
import R6_6_1BoundsB3
import R6_6_1BoundsB4
import R6_6_1BoundsB5
import R6_6_1BoundsB6
import R6_6_1BoundsB7
import R6_6_1BoundsB8
import R6_6_1BoundsB9
import R6_6_1BoundsB10
import R6_6_1BoundsB11
import R6_6_1BoundsB12
import R6_6_1BoundsB13
import R6_6_1BoundsB14
import R6_6_1BoundsB15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem bounds_check : ∀ m : Fin 4096, boundCheck 24 (table m.val) = true := by
  intro m
  by_cases h8 : m.val < 2048
  ·
    by_cases h4 : m.val < 1024
    ·
      by_cases h2 : m.val < 512
      ·
        by_cases h1 : m.val < 256
        ·
          have hb : m.val-0 < 256 := by omega
          have he : m.val-0+0 = m.val := by omega
          have hp := bounds_checkB0 ⟨m.val-0,hb⟩
          simpa only [he] using hp
        ·
          have hb : m.val-256 < 256 := by omega
          have he : m.val-256+256 = m.val := by omega
          have hp := bounds_checkB1 ⟨m.val-256,hb⟩
          simpa only [he] using hp
      ·
        by_cases h3 : m.val < 768
        ·
          have hb : m.val-512 < 256 := by omega
          have he : m.val-512+512 = m.val := by omega
          have hp := bounds_checkB2 ⟨m.val-512,hb⟩
          simpa only [he] using hp
        ·
          have hb : m.val-768 < 256 := by omega
          have he : m.val-768+768 = m.val := by omega
          have hp := bounds_checkB3 ⟨m.val-768,hb⟩
          simpa only [he] using hp
    ·
      by_cases h6 : m.val < 1536
      ·
        by_cases h5 : m.val < 1280
        ·
          have hb : m.val-1024 < 256 := by omega
          have he : m.val-1024+1024 = m.val := by omega
          have hp := bounds_checkB4 ⟨m.val-1024,hb⟩
          simpa only [he] using hp
        ·
          have hb : m.val-1280 < 256 := by omega
          have he : m.val-1280+1280 = m.val := by omega
          have hp := bounds_checkB5 ⟨m.val-1280,hb⟩
          simpa only [he] using hp
      ·
        by_cases h7 : m.val < 1792
        ·
          have hb : m.val-1536 < 256 := by omega
          have he : m.val-1536+1536 = m.val := by omega
          have hp := bounds_checkB6 ⟨m.val-1536,hb⟩
          simpa only [he] using hp
        ·
          have hb : m.val-1792 < 256 := by omega
          have he : m.val-1792+1792 = m.val := by omega
          have hp := bounds_checkB7 ⟨m.val-1792,hb⟩
          simpa only [he] using hp
  ·
    by_cases h12 : m.val < 3072
    ·
      by_cases h10 : m.val < 2560
      ·
        by_cases h9 : m.val < 2304
        ·
          have hb : m.val-2048 < 256 := by omega
          have he : m.val-2048+2048 = m.val := by omega
          have hp := bounds_checkB8 ⟨m.val-2048,hb⟩
          simpa only [he] using hp
        ·
          have hb : m.val-2304 < 256 := by omega
          have he : m.val-2304+2304 = m.val := by omega
          have hp := bounds_checkB9 ⟨m.val-2304,hb⟩
          simpa only [he] using hp
      ·
        by_cases h11 : m.val < 2816
        ·
          have hb : m.val-2560 < 256 := by omega
          have he : m.val-2560+2560 = m.val := by omega
          have hp := bounds_checkB10 ⟨m.val-2560,hb⟩
          simpa only [he] using hp
        ·
          have hb : m.val-2816 < 256 := by omega
          have he : m.val-2816+2816 = m.val := by omega
          have hp := bounds_checkB11 ⟨m.val-2816,hb⟩
          simpa only [he] using hp
    ·
      by_cases h14 : m.val < 3584
      ·
        by_cases h13 : m.val < 3328
        ·
          have hb : m.val-3072 < 256 := by omega
          have he : m.val-3072+3072 = m.val := by omega
          have hp := bounds_checkB12 ⟨m.val-3072,hb⟩
          simpa only [he] using hp
        ·
          have hb : m.val-3328 < 256 := by omega
          have he : m.val-3328+3328 = m.val := by omega
          have hp := bounds_checkB13 ⟨m.val-3328,hb⟩
          simpa only [he] using hp
      ·
        by_cases h15 : m.val < 3840
        ·
          have hb : m.val-3584 < 256 := by omega
          have he : m.val-3584+3584 = m.val := by omega
          have hp := bounds_checkB14 ⟨m.val-3584,hb⟩
          simpa only [he] using hp
        ·
          have hb : m.val-3840 < 256 := by omega
          have he : m.val-3840+3840 = m.val := by omega
          have hp := bounds_checkB15 ⟨m.val-3840,hb⟩
          simpa only [he] using hp
end R6_6_1
