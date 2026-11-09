import R8_6_0MergeB0
import R8_6_0MergeB1
import R8_6_0MergeB2
import R8_6_0MergeB3
import R8_6_0MergeB4
import R8_6_0MergeB5
import R8_6_0MergeB6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_check : ∀ u : Fin 256, halfCheck 8 32 table u.val = true := by
  intro u
  by_cases h3 : u.val < 177
  ·
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
        have hb : u.val-126 < 51 := by omega
        have he : u.val-126+126 = u.val := by omega
        have hp := merge_checkB2 ⟨u.val-126,hb⟩
        simpa only [he] using hp
  ·
    by_cases h5 : u.val < 237
    ·
      by_cases h4 : u.val < 211
      ·
        have hb : u.val-177 < 34 := by omega
        have he : u.val-177+177 = u.val := by omega
        have hp := merge_checkB3 ⟨u.val-177,hb⟩
        simpa only [he] using hp
      ·
        have hb : u.val-211 < 26 := by omega
        have he : u.val-211+211 = u.val := by omega
        have hp := merge_checkB4 ⟨u.val-211,hb⟩
        simpa only [he] using hp
    ·
      by_cases h6 : u.val < 252
      ·
        have hb : u.val-237 < 15 := by omega
        have he : u.val-237+237 = u.val := by omega
        have hp := merge_checkB5 ⟨u.val-237,hb⟩
        simpa only [he] using hp
      ·
        have hb : u.val-252 < 4 := by omega
        have he : u.val-252+252 = u.val := by omega
        have hp := merge_checkB6 ⟨u.val-252,hb⟩
        simpa only [he] using hp
end R8_6_0
