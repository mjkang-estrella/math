import R9_6_0Bounds0
import R9_6_0Bounds1
import R9_6_0Bounds2
import R9_6_0Bounds3
import R9_6_0Bounds4
import R9_6_0Bounds5
import R9_6_0Bounds6
import R9_6_0Bounds7
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem bounds_check : ∀ m : Fin 512, boundCheck 35 (table m.val) = true := by
  intro m
  by_cases h4 : m.val < 256
  ·
    by_cases h2 : m.val < 128
    ·
      by_cases h1 : m.val < 64
      ·
        have hb : m.val-0 < 64 := by omega
        have he : m.val-0+0 = m.val := by omega
        have hp := bounds_check0 ⟨m.val-0,hb⟩
        simpa only [he] using hp
      ·
        have hb : m.val-64 < 64 := by omega
        have he : m.val-64+64 = m.val := by omega
        have hp := bounds_check1 ⟨m.val-64,hb⟩
        simpa only [he] using hp
    ·
      by_cases h3 : m.val < 192
      ·
        have hb : m.val-128 < 64 := by omega
        have he : m.val-128+128 = m.val := by omega
        have hp := bounds_check2 ⟨m.val-128,hb⟩
        simpa only [he] using hp
      ·
        have hb : m.val-192 < 64 := by omega
        have he : m.val-192+192 = m.val := by omega
        have hp := bounds_check3 ⟨m.val-192,hb⟩
        simpa only [he] using hp
  ·
    by_cases h6 : m.val < 384
    ·
      by_cases h5 : m.val < 320
      ·
        have hb : m.val-256 < 64 := by omega
        have he : m.val-256+256 = m.val := by omega
        have hp := bounds_check4 ⟨m.val-256,hb⟩
        simpa only [he] using hp
      ·
        have hb : m.val-320 < 64 := by omega
        have he : m.val-320+320 = m.val := by omega
        have hp := bounds_check5 ⟨m.val-320,hb⟩
        simpa only [he] using hp
    ·
      by_cases h7 : m.val < 448
      ·
        have hb : m.val-384 < 64 := by omega
        have he : m.val-384+384 = m.val := by omega
        have hp := bounds_check6 ⟨m.val-384,hb⟩
        simpa only [he] using hp
      ·
        have hb : m.val-448 < 64 := by omega
        have he : m.val-448+448 = m.val := by omega
        have hp := bounds_check7 ⟨m.val-448,hb⟩
        simpa only [he] using hp

end R9_6_0
