import R9_5_0BoundsB0
import R9_5_0BoundsB1
import R9_5_0BoundsB2
import R9_5_0BoundsB3
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem bounds_check : ∀ m : Fin 1024, boundCheck 30 (table m.val) = true := by
  intro m
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
end R9_5_0
