import R7_5_0MergeB0
import R7_5_0MergeB1
import R7_5_0MergeB2
import R7_5_0MergeB3
import R7_5_0MergeB4
import R7_5_0MergeB5
import R7_5_0MergeB6
import R7_5_0MergeB7
import R7_5_0MergeB8
import R7_5_0MergeB9
import R7_5_0MergeB10
import R7_5_0MergeB11
import R7_5_0MergeB12
import R7_5_0MergeB13
import R7_5_0MergeB14
import R7_5_0MergeB15
import R7_5_0MergeB16
import R7_5_0MergeB17
import R7_5_0MergeB18
import R7_5_0MergeB19
import R7_5_0MergeB20
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_check : ∀ u : Fin 512, halfCheck 9 24 table u.val = true := by
  intro u
  by_cases h10 : u.val < 374
  ·
    by_cases h5 : u.val < 237
    ·
      by_cases h2 : u.val < 126
      ·
        by_cases h1 : u.val < 90
        ·
          have hb : u.val-0 < 90 := by omega
          have he : u.val-0+0 = u.val := by omega
          have hp := merge_checkB0 ⟨u.val-0,hb⟩
          simpa only [he] using hp
        ·
          have hb : u.val-90 < 36 := by omega
          have he : u.val-90+90 = u.val := by omega
          have hp := merge_checkB1 ⟨u.val-90,hb⟩
          simpa only [he] using hp
      ·
        by_cases h3 : u.val < 177
        ·
          have hb : u.val-126 < 51 := by omega
          have he : u.val-126+126 = u.val := by omega
          have hp := merge_checkB2 ⟨u.val-126,hb⟩
          simpa only [he] using hp
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
      by_cases h7 : u.val < 287
      ·
        by_cases h6 : u.val < 252
        ·
          have hb : u.val-237 < 15 := by omega
          have he : u.val-237+237 = u.val := by omega
          have hp := merge_checkB5 ⟨u.val-237,hb⟩
          simpa only [he] using hp
        ·
          have hb : u.val-252 < 35 := by omega
          have he : u.val-252+252 = u.val := by omega
          have hp := merge_checkB6 ⟨u.val-252,hb⟩
          simpa only [he] using hp
      ·
        by_cases h8 : u.val < 319
        ·
          have hb : u.val-287 < 32 := by omega
          have he : u.val-287+287 = u.val := by omega
          have hp := merge_checkB7 ⟨u.val-287,hb⟩
          simpa only [he] using hp
        ·
          by_cases h9 : u.val < 351
          ·
            have hb : u.val-319 < 32 := by omega
            have he : u.val-319+319 = u.val := by omega
            have hp := merge_checkB8 ⟨u.val-319,hb⟩
            simpa only [he] using hp
          ·
            have hb : u.val-351 < 23 := by omega
            have he : u.val-351+351 = u.val := by omega
            have hp := merge_checkB9 ⟨u.val-351,hb⟩
            simpa only [he] using hp
  ·
    by_cases h15 : u.val < 467
    ·
      by_cases h12 : u.val < 413
      ·
        by_cases h11 : u.val < 383
        ·
          have hb : u.val-374 < 9 := by omega
          have he : u.val-374+374 = u.val := by omega
          have hp := merge_checkB10 ⟨u.val-374,hb⟩
          simpa only [he] using hp
        ·
          have hb : u.val-383 < 30 := by omega
          have he : u.val-383+383 = u.val := by omega
          have hp := merge_checkB11 ⟨u.val-383,hb⟩
          simpa only [he] using hp
      ·
        by_cases h13 : u.val < 435
        ·
          have hb : u.val-413 < 22 := by omega
          have he : u.val-413+413 = u.val := by omega
          have hp := merge_checkB12 ⟨u.val-413,hb⟩
          simpa only [he] using hp
        ·
          by_cases h14 : u.val < 447
          ·
            have hb : u.val-435 < 12 := by omega
            have he : u.val-435+435 = u.val := by omega
            have hp := merge_checkB13 ⟨u.val-435,hb⟩
            simpa only [he] using hp
          ·
            have hb : u.val-447 < 20 := by omega
            have he : u.val-447+447 = u.val := by omega
            have hp := merge_checkB14 ⟨u.val-447,hb⟩
            simpa only [he] using hp
    ·
      by_cases h18 : u.val < 501
      ·
        by_cases h16 : u.val < 479
        ·
          have hb : u.val-467 < 12 := by omega
          have he : u.val-467+467 = u.val := by omega
          have hp := merge_checkB15 ⟨u.val-467,hb⟩
          simpa only [he] using hp
        ·
          by_cases h17 : u.val < 492
          ·
            have hb : u.val-479 < 13 := by omega
            have he : u.val-479+479 = u.val := by omega
            have hp := merge_checkB16 ⟨u.val-479,hb⟩
            simpa only [he] using hp
          ·
            have hb : u.val-492 < 9 := by omega
            have he : u.val-492+492 = u.val := by omega
            have hp := merge_checkB17 ⟨u.val-492,hb⟩
            simpa only [he] using hp
      ·
        by_cases h19 : u.val < 507
        ·
          have hb : u.val-501 < 6 := by omega
          have he : u.val-501+501 = u.val := by omega
          have hp := merge_checkB18 ⟨u.val-501,hb⟩
          simpa only [he] using hp
        ·
          by_cases h20 : u.val < 511
          ·
            have hb : u.val-507 < 4 := by omega
            have he : u.val-507+507 = u.val := by omega
            have hp := merge_checkB19 ⟨u.val-507,hb⟩
            simpa only [he] using hp
          ·
            have hb : u.val-511 < 1 := by omega
            have he : u.val-511+511 = u.val := by omega
            have hp := merge_checkB20 ⟨u.val-511,hb⟩
            simpa only [he] using hp
end R7_5_0
