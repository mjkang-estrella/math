import Link28_000
import Link28_001
import Link28_002
import Link28_003
import Link28_004
import Link28_005
import Link28_006
import Link28_007
import Link28_008
import Link28_009
import Link28_010
import Link28_011
import Link28_012
import Link28_013
import Link28_014
import Link28_015
import Link28_016
import Link28_017
import Link28_018
import Link28_019
import Link28_020
import Link28_021
import Link28_022
import Link28_023
import Link28_024
import Link28_025
import Link28_026
import Link28_027
import Link28_028
import Link28_029
import Link28_030
import Link28_031
import Link28_032
import Link28_033
import Link28_034
import Link28_035
import Link28_036
import Link28_037
import Link28_038
import Link28_039
import Link28_040
import Link28_041
import Link28_042
import Link28_043
import Link28_044
import Link28_045
import Link28_046
import Link28_047
import Link28_048
import Link28_049
import Link28_050
import Link28_051
import Link28_052
import Link28_053
import Link28_054
import Link28_055
import Link28_056
import Link28_057
import Link28_058
import Link28_059
import Link28_060
import Link28_061
import Link28_062
import Link28_063
import Link28_064
import Link28_065
import Link28_066
import Link28_067
import Link28_068
import Link28_069
import Link28_070
import Link28_071
import Link28_072
import Link28_073
import Link28_074
import Link28_075
import Link28_076
import Link28_077
import Link28_078
import Link28_079
import Link28_080
import Link28_081
import Link28_082
import Link28_083
import Link28_084
import Link28_085
import Link28_086
import Link28_087
import Link28_088
import Link28_089
import Link28_090
import Link28_091
import Link28_092
import Link28_093
import Link28_094
import Link28_095
import Link28_096
import Link28_097
import Link28_098
import Link28_099
import Link28_100
import Link28_101
import Link28_102
import Link28_103
import Link28_104
import Link28_105
import Link28_106
import Link28_107
import Link28_108
import Link28_109
import Link28_110
import Link28_111
import Link28_112
import Link28_113
import Link28_114
import Link28_115
import Link28_116
import Link28_117
import Link28_118
import Link28_119
import Link28_120
import Link28_121
import Link28_122
import Link28_123
import Link28_124
import Link28_125
import Link28_126
import Link28_127
import Link28_128
import Link28_129
import Link28_130
import Link28_131
import Link28_132
import Link28_133
import Link28_134
import Link28_135
import Link28_136
import Link28_137
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Schrijver
theorem table28_size : (vertexMasks28.toArray).size = 3185 := by decide
theorem table28_links (i : Fin 3185) : maskAt28 i.val = (vertexMasks28.toArray)[i.val]! ∧ (i.val+1 < (vertexMasks28.toArray).size → maskAt28 i.val < maskAt28 (i.val+1)) := by
  by_cases h0 : i.val < 32
  · exact tableLinkCheck_sound Link28_000_checked (by omega)
  by_cases h1 : i.val < 64
  · exact tableLinkCheck_sound Link28_001_checked (by omega)
  by_cases h2 : i.val < 96
  · exact tableLinkCheck_sound Link28_002_checked (by omega)
  by_cases h3 : i.val < 128
  · exact tableLinkCheck_sound Link28_003_checked (by omega)
  by_cases h4 : i.val < 160
  · exact tableLinkCheck_sound Link28_004_checked (by omega)
  by_cases h5 : i.val < 192
  · exact tableLinkCheck_sound Link28_005_checked (by omega)
  by_cases h6 : i.val < 224
  · exact tableLinkCheck_sound Link28_006_checked (by omega)
  by_cases h7 : i.val < 256
  · exact tableLinkCheck_sound Link28_007_checked (by omega)
  by_cases h8 : i.val < 288
  · exact tableLinkCheck_sound Link28_008_checked (by omega)
  by_cases h9 : i.val < 320
  · exact tableLinkCheck_sound Link28_009_checked (by omega)
  by_cases h10 : i.val < 352
  · exact tableLinkCheck_sound Link28_010_checked (by omega)
  by_cases h11 : i.val < 384
  · exact tableLinkCheck_sound Link28_011_checked (by omega)
  by_cases h12 : i.val < 416
  · exact tableLinkCheck_sound Link28_012_checked (by omega)
  by_cases h13 : i.val < 448
  · exact tableLinkCheck_sound Link28_013_checked (by omega)
  by_cases h14 : i.val < 480
  · exact tableLinkCheck_sound Link28_014_checked (by omega)
  by_cases h15 : i.val < 512
  · exact tableLinkCheck_sound Link28_015_checked (by omega)
  by_cases h16 : i.val < 544
  · exact tableLinkCheck_sound Link28_016_checked (by omega)
  by_cases h17 : i.val < 576
  · exact tableLinkCheck_sound Link28_017_checked (by omega)
  by_cases h18 : i.val < 608
  · exact tableLinkCheck_sound Link28_018_checked (by omega)
  by_cases h19 : i.val < 640
  · exact tableLinkCheck_sound Link28_019_checked (by omega)
  by_cases h20 : i.val < 672
  · exact tableLinkCheck_sound Link28_020_checked (by omega)
  by_cases h21 : i.val < 704
  · exact tableLinkCheck_sound Link28_021_checked (by omega)
  by_cases h22 : i.val < 736
  · exact tableLinkCheck_sound Link28_022_checked (by omega)
  by_cases h23 : i.val < 768
  · exact tableLinkCheck_sound Link28_023_checked (by omega)
  by_cases h24 : i.val < 800
  · exact tableLinkCheck_sound Link28_024_checked (by omega)
  by_cases h25 : i.val < 832
  · exact tableLinkCheck_sound Link28_025_checked (by omega)
  by_cases h26 : i.val < 864
  · exact tableLinkCheck_sound Link28_026_checked (by omega)
  by_cases h27 : i.val < 896
  · exact tableLinkCheck_sound Link28_027_checked (by omega)
  by_cases h28 : i.val < 928
  · exact tableLinkCheck_sound Link28_028_checked (by omega)
  by_cases h29 : i.val < 960
  · exact tableLinkCheck_sound Link28_029_checked (by omega)
  by_cases h30 : i.val < 992
  · exact tableLinkCheck_sound Link28_030_checked (by omega)
  by_cases h31 : i.val < 1024
  · exact tableLinkCheck_sound Link28_031_checked (by omega)
  by_cases h32 : i.val < 1056
  · exact tableLinkCheck_sound Link28_032_checked (by omega)
  by_cases h33 : i.val < 1088
  · exact tableLinkCheck_sound Link28_033_checked (by omega)
  by_cases h34 : i.val < 1120
  · exact tableLinkCheck_sound Link28_034_checked (by omega)
  by_cases h35 : i.val < 1152
  · exact tableLinkCheck_sound Link28_035_checked (by omega)
  by_cases h36 : i.val < 1184
  · exact tableLinkCheck_sound Link28_036_checked (by omega)
  by_cases h37 : i.val < 1216
  · exact tableLinkCheck_sound Link28_037_checked (by omega)
  by_cases h38 : i.val < 1248
  · exact tableLinkCheck_sound Link28_038_checked (by omega)
  by_cases h39 : i.val < 1280
  · exact tableLinkCheck_sound Link28_039_checked (by omega)
  by_cases h40 : i.val < 1312
  · exact tableLinkCheck_sound Link28_040_checked (by omega)
  by_cases h41 : i.val < 1344
  · exact tableLinkCheck_sound Link28_041_checked (by omega)
  by_cases h42 : i.val < 1376
  · exact tableLinkCheck_sound Link28_042_checked (by omega)
  by_cases h43 : i.val < 1408
  · exact tableLinkCheck_sound Link28_043_checked (by omega)
  by_cases h44 : i.val < 1440
  · exact tableLinkCheck_sound Link28_044_checked (by omega)
  by_cases h45 : i.val < 1472
  · exact tableLinkCheck_sound Link28_045_checked (by omega)
  by_cases h46 : i.val < 1504
  · exact tableLinkCheck_sound Link28_046_checked (by omega)
  by_cases h47 : i.val < 1536
  · exact tableLinkCheck_sound Link28_047_checked (by omega)
  by_cases h48 : i.val < 1568
  · exact tableLinkCheck_sound Link28_048_checked (by omega)
  by_cases h49 : i.val < 1600
  · exact tableLinkCheck_sound Link28_049_checked (by omega)
  by_cases h50 : i.val < 1632
  · exact tableLinkCheck_sound Link28_050_checked (by omega)
  by_cases h51 : i.val < 1664
  · exact tableLinkCheck_sound Link28_051_checked (by omega)
  by_cases h52 : i.val < 1696
  · exact tableLinkCheck_sound Link28_052_checked (by omega)
  by_cases h53 : i.val < 1728
  · exact tableLinkCheck_sound Link28_053_checked (by omega)
  by_cases h54 : i.val < 1760
  · exact tableLinkCheck_sound Link28_054_checked (by omega)
  by_cases h55 : i.val < 1792
  · exact tableLinkCheck_sound Link28_055_checked (by omega)
  by_cases h56 : i.val < 1824
  · exact tableLinkCheck_sound Link28_056_checked (by omega)
  by_cases h57 : i.val < 1856
  · exact tableLinkCheck_sound Link28_057_checked (by omega)
  by_cases h58 : i.val < 1888
  · exact tableLinkCheck_sound Link28_058_checked (by omega)
  by_cases h59 : i.val < 1920
  · exact tableLinkCheck_sound Link28_059_checked (by omega)
  by_cases h60 : i.val < 1952
  · exact tableLinkCheck_sound Link28_060_checked (by omega)
  by_cases h61 : i.val < 1984
  · exact tableLinkCheck_sound Link28_061_checked (by omega)
  by_cases h62 : i.val < 2000
  · exact tableLinkCheck_sound Link28_062_checked (by omega)
  by_cases h63 : i.val < 2016
  · exact tableLinkCheck_sound Link28_063_checked (by omega)
  by_cases h64 : i.val < 2032
  · exact tableLinkCheck_sound Link28_064_checked (by omega)
  by_cases h65 : i.val < 2048
  · exact tableLinkCheck_sound Link28_065_checked (by omega)
  by_cases h66 : i.val < 2064
  · exact tableLinkCheck_sound Link28_066_checked (by omega)
  by_cases h67 : i.val < 2080
  · exact tableLinkCheck_sound Link28_067_checked (by omega)
  by_cases h68 : i.val < 2096
  · exact tableLinkCheck_sound Link28_068_checked (by omega)
  by_cases h69 : i.val < 2112
  · exact tableLinkCheck_sound Link28_069_checked (by omega)
  by_cases h70 : i.val < 2128
  · exact tableLinkCheck_sound Link28_070_checked (by omega)
  by_cases h71 : i.val < 2144
  · exact tableLinkCheck_sound Link28_071_checked (by omega)
  by_cases h72 : i.val < 2160
  · exact tableLinkCheck_sound Link28_072_checked (by omega)
  by_cases h73 : i.val < 2176
  · exact tableLinkCheck_sound Link28_073_checked (by omega)
  by_cases h74 : i.val < 2192
  · exact tableLinkCheck_sound Link28_074_checked (by omega)
  by_cases h75 : i.val < 2208
  · exact tableLinkCheck_sound Link28_075_checked (by omega)
  by_cases h76 : i.val < 2224
  · exact tableLinkCheck_sound Link28_076_checked (by omega)
  by_cases h77 : i.val < 2240
  · exact tableLinkCheck_sound Link28_077_checked (by omega)
  by_cases h78 : i.val < 2256
  · exact tableLinkCheck_sound Link28_078_checked (by omega)
  by_cases h79 : i.val < 2272
  · exact tableLinkCheck_sound Link28_079_checked (by omega)
  by_cases h80 : i.val < 2288
  · exact tableLinkCheck_sound Link28_080_checked (by omega)
  by_cases h81 : i.val < 2304
  · exact tableLinkCheck_sound Link28_081_checked (by omega)
  by_cases h82 : i.val < 2320
  · exact tableLinkCheck_sound Link28_082_checked (by omega)
  by_cases h83 : i.val < 2336
  · exact tableLinkCheck_sound Link28_083_checked (by omega)
  by_cases h84 : i.val < 2352
  · exact tableLinkCheck_sound Link28_084_checked (by omega)
  by_cases h85 : i.val < 2368
  · exact tableLinkCheck_sound Link28_085_checked (by omega)
  by_cases h86 : i.val < 2384
  · exact tableLinkCheck_sound Link28_086_checked (by omega)
  by_cases h87 : i.val < 2400
  · exact tableLinkCheck_sound Link28_087_checked (by omega)
  by_cases h88 : i.val < 2416
  · exact tableLinkCheck_sound Link28_088_checked (by omega)
  by_cases h89 : i.val < 2432
  · exact tableLinkCheck_sound Link28_089_checked (by omega)
  by_cases h90 : i.val < 2448
  · exact tableLinkCheck_sound Link28_090_checked (by omega)
  by_cases h91 : i.val < 2464
  · exact tableLinkCheck_sound Link28_091_checked (by omega)
  by_cases h92 : i.val < 2480
  · exact tableLinkCheck_sound Link28_092_checked (by omega)
  by_cases h93 : i.val < 2496
  · exact tableLinkCheck_sound Link28_093_checked (by omega)
  by_cases h94 : i.val < 2512
  · exact tableLinkCheck_sound Link28_094_checked (by omega)
  by_cases h95 : i.val < 2528
  · exact tableLinkCheck_sound Link28_095_checked (by omega)
  by_cases h96 : i.val < 2544
  · exact tableLinkCheck_sound Link28_096_checked (by omega)
  by_cases h97 : i.val < 2560
  · exact tableLinkCheck_sound Link28_097_checked (by omega)
  by_cases h98 : i.val < 2576
  · exact tableLinkCheck_sound Link28_098_checked (by omega)
  by_cases h99 : i.val < 2592
  · exact tableLinkCheck_sound Link28_099_checked (by omega)
  by_cases h100 : i.val < 2608
  · exact tableLinkCheck_sound Link28_100_checked (by omega)
  by_cases h101 : i.val < 2624
  · exact tableLinkCheck_sound Link28_101_checked (by omega)
  by_cases h102 : i.val < 2640
  · exact tableLinkCheck_sound Link28_102_checked (by omega)
  by_cases h103 : i.val < 2656
  · exact tableLinkCheck_sound Link28_103_checked (by omega)
  by_cases h104 : i.val < 2672
  · exact tableLinkCheck_sound Link28_104_checked (by omega)
  by_cases h105 : i.val < 2688
  · exact tableLinkCheck_sound Link28_105_checked (by omega)
  by_cases h106 : i.val < 2704
  · exact tableLinkCheck_sound Link28_106_checked (by omega)
  by_cases h107 : i.val < 2720
  · exact tableLinkCheck_sound Link28_107_checked (by omega)
  by_cases h108 : i.val < 2736
  · exact tableLinkCheck_sound Link28_108_checked (by omega)
  by_cases h109 : i.val < 2752
  · exact tableLinkCheck_sound Link28_109_checked (by omega)
  by_cases h110 : i.val < 2768
  · exact tableLinkCheck_sound Link28_110_checked (by omega)
  by_cases h111 : i.val < 2784
  · exact tableLinkCheck_sound Link28_111_checked (by omega)
  by_cases h112 : i.val < 2800
  · exact tableLinkCheck_sound Link28_112_checked (by omega)
  by_cases h113 : i.val < 2816
  · exact tableLinkCheck_sound Link28_113_checked (by omega)
  by_cases h114 : i.val < 2832
  · exact tableLinkCheck_sound Link28_114_checked (by omega)
  by_cases h115 : i.val < 2848
  · exact tableLinkCheck_sound Link28_115_checked (by omega)
  by_cases h116 : i.val < 2864
  · exact tableLinkCheck_sound Link28_116_checked (by omega)
  by_cases h117 : i.val < 2880
  · exact tableLinkCheck_sound Link28_117_checked (by omega)
  by_cases h118 : i.val < 2896
  · exact tableLinkCheck_sound Link28_118_checked (by omega)
  by_cases h119 : i.val < 2912
  · exact tableLinkCheck_sound Link28_119_checked (by omega)
  by_cases h120 : i.val < 2928
  · exact tableLinkCheck_sound Link28_120_checked (by omega)
  by_cases h121 : i.val < 2944
  · exact tableLinkCheck_sound Link28_121_checked (by omega)
  by_cases h122 : i.val < 2960
  · exact tableLinkCheck_sound Link28_122_checked (by omega)
  by_cases h123 : i.val < 2976
  · exact tableLinkCheck_sound Link28_123_checked (by omega)
  by_cases h124 : i.val < 2992
  · exact tableLinkCheck_sound Link28_124_checked (by omega)
  by_cases h125 : i.val < 3008
  · exact tableLinkCheck_sound Link28_125_checked (by omega)
  by_cases h126 : i.val < 3024
  · exact tableLinkCheck_sound Link28_126_checked (by omega)
  by_cases h127 : i.val < 3040
  · exact tableLinkCheck_sound Link28_127_checked (by omega)
  by_cases h128 : i.val < 3056
  · exact tableLinkCheck_sound Link28_128_checked (by omega)
  by_cases h129 : i.val < 3072
  · exact tableLinkCheck_sound Link28_129_checked (by omega)
  by_cases h130 : i.val < 3088
  · exact tableLinkCheck_sound Link28_130_checked (by omega)
  by_cases h131 : i.val < 3104
  · exact tableLinkCheck_sound Link28_131_checked (by omega)
  by_cases h132 : i.val < 3120
  · exact tableLinkCheck_sound Link28_132_checked (by omega)
  by_cases h133 : i.val < 3136
  · exact tableLinkCheck_sound Link28_133_checked (by omega)
  by_cases h134 : i.val < 3152
  · exact tableLinkCheck_sound Link28_134_checked (by omega)
  by_cases h135 : i.val < 3168
  · exact tableLinkCheck_sound Link28_135_checked (by omega)
  by_cases h136 : i.val < 3184
  · exact tableLinkCheck_sound Link28_136_checked (by omega)
  exact tableLinkCheck_sound Link28_137_checked (by have := i.isLt; omega)
theorem maskAt28_lookup (i : Fin 3185) : maskAt28 i.val = (vertexMasks28.toArray)[i.val]! := (table28_links i).1

theorem maskAt28_injective : Function.Injective (fun i : Fin 3185 => maskAt28 i.val) := by
  apply (bounded_strictMono maskAt28 ?_).injective
  intro i hi
  exact (table28_links ⟨i, by omega⟩).2 (by rw [table28_size]; exact hi)
end Schrijver
