import Label27_000
import Label27_001
import Label27_002
import Label27_003
import Label27_004
import Label27_005
import Label27_006
import Label27_007
import Label27_008
import Label27_009
import Label27_010
import Label27_011
import Label27_012
import Label27_013
import Label27_014
import Label27_015
import Label27_016
import Label27_017
import Label27_018
import Label27_019
import Label27_020
import Label27_021
import Label27_022
import Label27_023
import Label27_024
import Label27_025
import Label27_026
import Label27_027
import Label27_028
import Label27_029
import Label27_030
import Label27_031
import Label27_032
import Label27_033
import Label27_034
import Label27_035
import Label27_036
import Label27_037
import Label27_038
import Label27_039
import Label27_040
import Label27_041
import Label27_042
import Label27_043
import Label27_044
import Label27_045
import Label27_046
import Label27_047
import Label27_048
import Label27_049
import Label27_050
import Label27_051

set_option exponentiation.threshold 200000
namespace Schrijver
theorem labels27_edge : ∀ u v, (indexedGraph 819 maskAt27).Adj u v → indexDepth Tree27_000.depths v ≤ indexDepth Tree27_000.depths u + 1 := by
  intro u v he
  by_cases h0 : u.val < 16
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_000_checked u v (by omega) he
  by_cases h1 : u.val < 32
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_001_checked u v (by omega) he
  by_cases h2 : u.val < 48
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_002_checked u v (by omega) he
  by_cases h3 : u.val < 64
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_003_checked u v (by omega) he
  by_cases h4 : u.val < 80
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_004_checked u v (by omega) he
  by_cases h5 : u.val < 96
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_005_checked u v (by omega) he
  by_cases h6 : u.val < 112
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_006_checked u v (by omega) he
  by_cases h7 : u.val < 128
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_007_checked u v (by omega) he
  by_cases h8 : u.val < 144
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_008_checked u v (by omega) he
  by_cases h9 : u.val < 160
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_009_checked u v (by omega) he
  by_cases h10 : u.val < 176
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_010_checked u v (by omega) he
  by_cases h11 : u.val < 192
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_011_checked u v (by omega) he
  by_cases h12 : u.val < 208
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_012_checked u v (by omega) he
  by_cases h13 : u.val < 224
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_013_checked u v (by omega) he
  by_cases h14 : u.val < 240
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_014_checked u v (by omega) he
  by_cases h15 : u.val < 256
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_015_checked u v (by omega) he
  by_cases h16 : u.val < 272
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_016_checked u v (by omega) he
  by_cases h17 : u.val < 288
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_017_checked u v (by omega) he
  by_cases h18 : u.val < 304
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_018_checked u v (by omega) he
  by_cases h19 : u.val < 320
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_019_checked u v (by omega) he
  by_cases h20 : u.val < 336
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_020_checked u v (by omega) he
  by_cases h21 : u.val < 352
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_021_checked u v (by omega) he
  by_cases h22 : u.val < 368
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_022_checked u v (by omega) he
  by_cases h23 : u.val < 384
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_023_checked u v (by omega) he
  by_cases h24 : u.val < 400
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_024_checked u v (by omega) he
  by_cases h25 : u.val < 416
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_025_checked u v (by omega) he
  by_cases h26 : u.val < 432
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_026_checked u v (by omega) he
  by_cases h27 : u.val < 448
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_027_checked u v (by omega) he
  by_cases h28 : u.val < 464
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_028_checked u v (by omega) he
  by_cases h29 : u.val < 480
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_029_checked u v (by omega) he
  by_cases h30 : u.val < 496
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_030_checked u v (by omega) he
  by_cases h31 : u.val < 512
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_031_checked u v (by omega) he
  by_cases h32 : u.val < 528
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_032_checked u v (by omega) he
  by_cases h33 : u.val < 544
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_033_checked u v (by omega) he
  by_cases h34 : u.val < 560
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_034_checked u v (by omega) he
  by_cases h35 : u.val < 576
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_035_checked u v (by omega) he
  by_cases h36 : u.val < 592
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_036_checked u v (by omega) he
  by_cases h37 : u.val < 608
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_037_checked u v (by omega) he
  by_cases h38 : u.val < 624
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_038_checked u v (by omega) he
  by_cases h39 : u.val < 640
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_039_checked u v (by omega) he
  by_cases h40 : u.val < 656
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_040_checked u v (by omega) he
  by_cases h41 : u.val < 672
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_041_checked u v (by omega) he
  by_cases h42 : u.val < 688
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_042_checked u v (by omega) he
  by_cases h43 : u.val < 704
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_043_checked u v (by omega) he
  by_cases h44 : u.val < 720
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_044_checked u v (by omega) he
  by_cases h45 : u.val < 736
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_045_checked u v (by omega) he
  by_cases h46 : u.val < 752
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_046_checked u v (by omega) he
  by_cases h47 : u.val < 768
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_047_checked u v (by omega) he
  by_cases h48 : u.val < 784
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_048_checked u v (by omega) he
  by_cases h49 : u.val < 800
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_049_checked u v (by omega) he
  by_cases h50 : u.val < 816
  · exact labelRangeCheck_sound _ _ _ _ _ Label27_050_checked u v (by omega) he
  exact labelRangeCheck_sound _ _ _ _ _ Label27_051_checked u v (by have := u.isLt; omega) he
theorem indexed_distance8 : 8 ≤ (indexedGraph 819 maskAt27).dist (⟨29, by decide⟩) (⟨143, by decide⟩) := by
  have h := labels_lower_distance (indexDepth Tree27_000.depths) labels27_edge (a := (⟨29, by decide⟩ : Fin 819)) (b := (⟨143, by decide⟩ : Fin 819)) (by decide) (Tree27_000.sound.1.preconnected _ _)
  have hv : indexDepth Tree27_000.depths (⟨143, by decide⟩ : Fin 819) = 8 := by decide
  rw [hv] at h
  exact h
end Schrijver
