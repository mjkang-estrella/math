import R8_7_0MergeB0
import R8_7_0MergeB1
import R8_7_0MergeB2
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_7_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_check : ∀ u : Fin 128, halfCheck 7 36 table u.val = true := by
  intro u
  by_cases h1 : u.val < 90
  ·
    have hb : u.val-0 < 90 := by omega
    have he : u.val-0+0 = u.val := by omega
    have hp := merge_checkB0 ⟨u.val-0,hb⟩
    simpa only [he] using hp
  ·
    by_cases h2 : u.val < 126
    ·
      have hb : u.val-90 < 36 := by omega
      have he : u.val-90+90 = u.val := by omega
      have hp := merge_checkB1 ⟨u.val-90,hb⟩
      simpa only [he] using hp
    ·
      have hb : u.val-126 < 2 := by omega
      have he : u.val-126+126 = u.val := by omega
      have hp := merge_checkB2 ⟨u.val-126,hb⟩
      simpa only [he] using hp
end R8_7_0
