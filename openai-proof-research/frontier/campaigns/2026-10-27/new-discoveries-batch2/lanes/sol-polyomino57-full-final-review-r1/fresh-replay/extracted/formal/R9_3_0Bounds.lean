import R9_3_0BoundsB0
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_3_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem bounds_check : ∀ m : Fin 64, boundCheck 20 (table m.val) = true := by
  intro m
  have hb : m.val-0 < 64 := by omega
  have he : m.val-0+0 = m.val := by omega
  have hp := bounds_checkB0 ⟨m.val-0,hb⟩
  simpa only [he] using hp
end R9_3_0
