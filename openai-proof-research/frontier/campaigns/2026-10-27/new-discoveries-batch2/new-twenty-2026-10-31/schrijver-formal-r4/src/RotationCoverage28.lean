import Rotation28_000
import Rotation28_001
import Rotation28_002
import Rotation28_003
import Rotation28_004
import Rotation28_005
import Rotation28_006
import Rotation28_007
import Rotation28_008
import Rotation28_009
import Rotation28_010
import Rotation28_011
import Rotation28_012
import Rotation28_013
import Rotation28_014
import Rotation28_015
import Rotation28_016
import Rotation28_017
import Rotation28_018
import Rotation28_019
import Rotation28_020
import Rotation28_021
import Rotation28_022
import Rotation28_023
import Rotation28_024
import Rotation28_025
import Rotation28_026
import Rotation28_027
import Rotation28_028
import Rotation28_029
import Rotation28_030
import Rotation28_031
import Rotation28_032
import Rotation28_033
import Rotation28_034
import Rotation28_035
import Rotation28_036
import Rotation28_037
import Rotation28_038
import Rotation28_039
import Rotation28_040
import Rotation28_041
import Rotation28_042
import Rotation28_043
import Rotation28_044
import Rotation28_045
import Rotation28_046
import Rotation28_047
import Rotation28_048
import Rotation28_049
import Rotation28_050
import Rotation28_051
import Rotation28_052
import Rotation28_053
import Rotation28_054
import Rotation28_055
import Rotation28_056
import Rotation28_057
import Rotation28_058
import Rotation28_059
import Rotation28_060
import Rotation28_061
import Rotation28_062
import Rotation28_063
import Rotation28_064
import Rotation28_065
import Rotation28_066
import Rotation28_067
import Rotation28_068
import Rotation28_069
import Rotation28_070
import Rotation28_071
import Rotation28_072
import Rotation28_073
import Rotation28_074
import Rotation28_075
import Rotation28_076
import Rotation28_077
import Rotation28_078
import Rotation28_079
import Rotation28_080
import Rotation28_081
import Rotation28_082
import Rotation28_083
import Rotation28_084
import Rotation28_085
import Rotation28_086
import Rotation28_087
import Rotation28_088
import Rotation28_089
import Rotation28_090
import Rotation28_091
import Rotation28_092
import Rotation28_093
import Rotation28_094
import Rotation28_095
import Rotation28_096
import Rotation28_097
import Rotation28_098
import Rotation28_099
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem indexed_rotation_coverage28 (i : Fin 3185) :
    ∃ t : Fin 28, ∃ r : Fin 3185, r ∈ upperRoots28 ∧
      rotateVertex t (indexedVertex maskAt28 masks28_valid_at i) =
        indexedVertex maskAt28 masks28_valid_at r := by
  by_cases h0 : i.val < 32
  · exact rotationChunk_sound Rotation28_000_checked i (by omega)
  by_cases h1 : i.val < 64
  · exact rotationChunk_sound Rotation28_001_checked i (by omega)
  by_cases h2 : i.val < 96
  · exact rotationChunk_sound Rotation28_002_checked i (by omega)
  by_cases h3 : i.val < 128
  · exact rotationChunk_sound Rotation28_003_checked i (by omega)
  by_cases h4 : i.val < 160
  · exact rotationChunk_sound Rotation28_004_checked i (by omega)
  by_cases h5 : i.val < 192
  · exact rotationChunk_sound Rotation28_005_checked i (by omega)
  by_cases h6 : i.val < 224
  · exact rotationChunk_sound Rotation28_006_checked i (by omega)
  by_cases h7 : i.val < 256
  · exact rotationChunk_sound Rotation28_007_checked i (by omega)
  by_cases h8 : i.val < 288
  · exact rotationChunk_sound Rotation28_008_checked i (by omega)
  by_cases h9 : i.val < 320
  · exact rotationChunk_sound Rotation28_009_checked i (by omega)
  by_cases h10 : i.val < 352
  · exact rotationChunk_sound Rotation28_010_checked i (by omega)
  by_cases h11 : i.val < 384
  · exact rotationChunk_sound Rotation28_011_checked i (by omega)
  by_cases h12 : i.val < 416
  · exact rotationChunk_sound Rotation28_012_checked i (by omega)
  by_cases h13 : i.val < 448
  · exact rotationChunk_sound Rotation28_013_checked i (by omega)
  by_cases h14 : i.val < 480
  · exact rotationChunk_sound Rotation28_014_checked i (by omega)
  by_cases h15 : i.val < 512
  · exact rotationChunk_sound Rotation28_015_checked i (by omega)
  by_cases h16 : i.val < 544
  · exact rotationChunk_sound Rotation28_016_checked i (by omega)
  by_cases h17 : i.val < 576
  · exact rotationChunk_sound Rotation28_017_checked i (by omega)
  by_cases h18 : i.val < 608
  · exact rotationChunk_sound Rotation28_018_checked i (by omega)
  by_cases h19 : i.val < 640
  · exact rotationChunk_sound Rotation28_019_checked i (by omega)
  by_cases h20 : i.val < 672
  · exact rotationChunk_sound Rotation28_020_checked i (by omega)
  by_cases h21 : i.val < 704
  · exact rotationChunk_sound Rotation28_021_checked i (by omega)
  by_cases h22 : i.val < 736
  · exact rotationChunk_sound Rotation28_022_checked i (by omega)
  by_cases h23 : i.val < 768
  · exact rotationChunk_sound Rotation28_023_checked i (by omega)
  by_cases h24 : i.val < 800
  · exact rotationChunk_sound Rotation28_024_checked i (by omega)
  by_cases h25 : i.val < 832
  · exact rotationChunk_sound Rotation28_025_checked i (by omega)
  by_cases h26 : i.val < 864
  · exact rotationChunk_sound Rotation28_026_checked i (by omega)
  by_cases h27 : i.val < 896
  · exact rotationChunk_sound Rotation28_027_checked i (by omega)
  by_cases h28 : i.val < 928
  · exact rotationChunk_sound Rotation28_028_checked i (by omega)
  by_cases h29 : i.val < 960
  · exact rotationChunk_sound Rotation28_029_checked i (by omega)
  by_cases h30 : i.val < 992
  · exact rotationChunk_sound Rotation28_030_checked i (by omega)
  by_cases h31 : i.val < 1024
  · exact rotationChunk_sound Rotation28_031_checked i (by omega)
  by_cases h32 : i.val < 1056
  · exact rotationChunk_sound Rotation28_032_checked i (by omega)
  by_cases h33 : i.val < 1088
  · exact rotationChunk_sound Rotation28_033_checked i (by omega)
  by_cases h34 : i.val < 1120
  · exact rotationChunk_sound Rotation28_034_checked i (by omega)
  by_cases h35 : i.val < 1152
  · exact rotationChunk_sound Rotation28_035_checked i (by omega)
  by_cases h36 : i.val < 1184
  · exact rotationChunk_sound Rotation28_036_checked i (by omega)
  by_cases h37 : i.val < 1216
  · exact rotationChunk_sound Rotation28_037_checked i (by omega)
  by_cases h38 : i.val < 1248
  · exact rotationChunk_sound Rotation28_038_checked i (by omega)
  by_cases h39 : i.val < 1280
  · exact rotationChunk_sound Rotation28_039_checked i (by omega)
  by_cases h40 : i.val < 1312
  · exact rotationChunk_sound Rotation28_040_checked i (by omega)
  by_cases h41 : i.val < 1344
  · exact rotationChunk_sound Rotation28_041_checked i (by omega)
  by_cases h42 : i.val < 1376
  · exact rotationChunk_sound Rotation28_042_checked i (by omega)
  by_cases h43 : i.val < 1408
  · exact rotationChunk_sound Rotation28_043_checked i (by omega)
  by_cases h44 : i.val < 1440
  · exact rotationChunk_sound Rotation28_044_checked i (by omega)
  by_cases h45 : i.val < 1472
  · exact rotationChunk_sound Rotation28_045_checked i (by omega)
  by_cases h46 : i.val < 1504
  · exact rotationChunk_sound Rotation28_046_checked i (by omega)
  by_cases h47 : i.val < 1536
  · exact rotationChunk_sound Rotation28_047_checked i (by omega)
  by_cases h48 : i.val < 1568
  · exact rotationChunk_sound Rotation28_048_checked i (by omega)
  by_cases h49 : i.val < 1600
  · exact rotationChunk_sound Rotation28_049_checked i (by omega)
  by_cases h50 : i.val < 1632
  · exact rotationChunk_sound Rotation28_050_checked i (by omega)
  by_cases h51 : i.val < 1664
  · exact rotationChunk_sound Rotation28_051_checked i (by omega)
  by_cases h52 : i.val < 1696
  · exact rotationChunk_sound Rotation28_052_checked i (by omega)
  by_cases h53 : i.val < 1728
  · exact rotationChunk_sound Rotation28_053_checked i (by omega)
  by_cases h54 : i.val < 1760
  · exact rotationChunk_sound Rotation28_054_checked i (by omega)
  by_cases h55 : i.val < 1792
  · exact rotationChunk_sound Rotation28_055_checked i (by omega)
  by_cases h56 : i.val < 1824
  · exact rotationChunk_sound Rotation28_056_checked i (by omega)
  by_cases h57 : i.val < 1856
  · exact rotationChunk_sound Rotation28_057_checked i (by omega)
  by_cases h58 : i.val < 1888
  · exact rotationChunk_sound Rotation28_058_checked i (by omega)
  by_cases h59 : i.val < 1920
  · exact rotationChunk_sound Rotation28_059_checked i (by omega)
  by_cases h60 : i.val < 1952
  · exact rotationChunk_sound Rotation28_060_checked i (by omega)
  by_cases h61 : i.val < 1984
  · exact rotationChunk_sound Rotation28_061_checked i (by omega)
  by_cases h62 : i.val < 2016
  · exact rotationChunk_sound Rotation28_062_checked i (by omega)
  by_cases h63 : i.val < 2048
  · exact rotationChunk_sound Rotation28_063_checked i (by omega)
  by_cases h64 : i.val < 2080
  · exact rotationChunk_sound Rotation28_064_checked i (by omega)
  by_cases h65 : i.val < 2112
  · exact rotationChunk_sound Rotation28_065_checked i (by omega)
  by_cases h66 : i.val < 2144
  · exact rotationChunk_sound Rotation28_066_checked i (by omega)
  by_cases h67 : i.val < 2176
  · exact rotationChunk_sound Rotation28_067_checked i (by omega)
  by_cases h68 : i.val < 2208
  · exact rotationChunk_sound Rotation28_068_checked i (by omega)
  by_cases h69 : i.val < 2240
  · exact rotationChunk_sound Rotation28_069_checked i (by omega)
  by_cases h70 : i.val < 2272
  · exact rotationChunk_sound Rotation28_070_checked i (by omega)
  by_cases h71 : i.val < 2304
  · exact rotationChunk_sound Rotation28_071_checked i (by omega)
  by_cases h72 : i.val < 2336
  · exact rotationChunk_sound Rotation28_072_checked i (by omega)
  by_cases h73 : i.val < 2368
  · exact rotationChunk_sound Rotation28_073_checked i (by omega)
  by_cases h74 : i.val < 2400
  · exact rotationChunk_sound Rotation28_074_checked i (by omega)
  by_cases h75 : i.val < 2432
  · exact rotationChunk_sound Rotation28_075_checked i (by omega)
  by_cases h76 : i.val < 2464
  · exact rotationChunk_sound Rotation28_076_checked i (by omega)
  by_cases h77 : i.val < 2496
  · exact rotationChunk_sound Rotation28_077_checked i (by omega)
  by_cases h78 : i.val < 2528
  · exact rotationChunk_sound Rotation28_078_checked i (by omega)
  by_cases h79 : i.val < 2560
  · exact rotationChunk_sound Rotation28_079_checked i (by omega)
  by_cases h80 : i.val < 2592
  · exact rotationChunk_sound Rotation28_080_checked i (by omega)
  by_cases h81 : i.val < 2624
  · exact rotationChunk_sound Rotation28_081_checked i (by omega)
  by_cases h82 : i.val < 2656
  · exact rotationChunk_sound Rotation28_082_checked i (by omega)
  by_cases h83 : i.val < 2688
  · exact rotationChunk_sound Rotation28_083_checked i (by omega)
  by_cases h84 : i.val < 2720
  · exact rotationChunk_sound Rotation28_084_checked i (by omega)
  by_cases h85 : i.val < 2752
  · exact rotationChunk_sound Rotation28_085_checked i (by omega)
  by_cases h86 : i.val < 2784
  · exact rotationChunk_sound Rotation28_086_checked i (by omega)
  by_cases h87 : i.val < 2816
  · exact rotationChunk_sound Rotation28_087_checked i (by omega)
  by_cases h88 : i.val < 2848
  · exact rotationChunk_sound Rotation28_088_checked i (by omega)
  by_cases h89 : i.val < 2880
  · exact rotationChunk_sound Rotation28_089_checked i (by omega)
  by_cases h90 : i.val < 2912
  · exact rotationChunk_sound Rotation28_090_checked i (by omega)
  by_cases h91 : i.val < 2944
  · exact rotationChunk_sound Rotation28_091_checked i (by omega)
  by_cases h92 : i.val < 2976
  · exact rotationChunk_sound Rotation28_092_checked i (by omega)
  by_cases h93 : i.val < 3008
  · exact rotationChunk_sound Rotation28_093_checked i (by omega)
  by_cases h94 : i.val < 3040
  · exact rotationChunk_sound Rotation28_094_checked i (by omega)
  by_cases h95 : i.val < 3072
  · exact rotationChunk_sound Rotation28_095_checked i (by omega)
  by_cases h96 : i.val < 3104
  · exact rotationChunk_sound Rotation28_096_checked i (by omega)
  by_cases h97 : i.val < 3136
  · exact rotationChunk_sound Rotation28_097_checked i (by omega)
  by_cases h98 : i.val < 3168
  · exact rotationChunk_sound Rotation28_098_checked i (by omega)
  exact rotationChunk_sound Rotation28_099_checked i (by have := i.isLt; omega)

theorem rotation_coverage28_from_enumeration (h : Enumeration28) :
    RotationRepresentativeCoverage28 := by
  intro a
  obtain ⟨i, hi⟩ := (literalIso28 h).toEquiv.surjective a
  subst a
  exact indexed_rotation_coverage28 i

theorem mathdb_352827_round4_conditional (h27 : Enumeration27) (h28 : Enumeration28) :
    ¬ SchrijverUnitGap :=
  mathdb_352827_round3_conditional h27 h28 (rotation_coverage28_from_enumeration h28)
end Schrijver
