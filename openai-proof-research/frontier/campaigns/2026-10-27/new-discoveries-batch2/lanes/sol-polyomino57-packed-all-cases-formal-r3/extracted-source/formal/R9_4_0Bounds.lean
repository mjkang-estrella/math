import R9_4_0BoundsB0
import R9_4_0BoundsB1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_4_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem bounds_check : ∀ m : Fin 512, boundCheck 25 (table m.val) = true := by
  intro m
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
end R9_4_0
