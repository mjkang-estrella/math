import R9_3_0MergeB0
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_3_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_check : ∀ u : Fin 64, halfCheck 6 20 table u.val = true := by
  intro u
  have hb : u.val-0 < 64 := by omega
  have he : u.val-0+0 = u.val := by omega
  have hp := merge_checkB0 ⟨u.val-0,hb⟩
  simpa only [he] using hp
end R9_3_0
