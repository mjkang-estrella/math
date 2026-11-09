import MetricTransport
import Tree28_000
import Tree28_001
import Tree28_002
import Tree28_003
import Tree28_004
import Tree28_005
import Tree28_006
import Tree28_007
import Tree28_008
import Tree28_009
import Tree28_010
import Tree28_011
import Tree28_012
import Tree28_013
import Tree28_014
import Tree28_015
import Tree28_016
import Tree28_017
import Tree28_018
import Tree28_019
import Tree28_020
import Tree28_021
import Tree28_022
import Tree28_023
import Tree28_024
import Tree28_025
import Tree28_026
import Tree28_027
import Tree28_028
import Tree28_029
import Tree28_030
import Tree28_031
import Tree28_032
import Tree28_033
import Tree28_034
import Tree28_035
import Tree28_036
import Tree28_037
import Tree28_038
import Tree28_039
import Tree28_040
import Tree28_041
import Tree28_042
import Tree28_043
import Tree28_044
import Tree28_045
import Tree28_046
import Tree28_047
import Tree28_048
import Tree28_049
import Tree28_050
import Tree28_051
import Tree28_052
import Tree28_053
import Tree28_054
import Tree28_055
import Tree28_056
import Tree28_057
import Tree28_058
import Tree28_059
import Tree28_060
import Tree28_061
import Tree28_062
import Tree28_063
import Tree28_064
import Tree28_065
import Tree28_066
import Tree28_067
import Tree28_068
import Tree28_069
import Tree28_070
import Tree28_071
import Tree28_072
import Tree28_073
import Tree28_074
import Tree28_075
import Tree28_076
import Tree28_077
import Tree28_078
import Tree28_079
import Tree28_080
import Tree28_081
import Tree28_082
import Tree28_083
import Tree28_084
import Tree28_085
import Tree28_086
import Tree28_087
import Tree28_088
import Tree28_089
import Tree28_090
import Tree28_091
import Tree28_092
import Tree28_093
import Tree28_094
import Tree28_095
import Tree28_096
import Tree28_097
import Tree28_098
import Tree28_099
import Tree28_100
import Tree28_101
import Tree28_102
import Tree28_103
import Tree28_104
import Tree28_105
import Tree28_106
import Tree28_107
import Tree28_108
import Tree28_109
import Tree28_110
import Tree28_111
import Tree28_112
import Tree28_113
import Tree28_114
import Tree28_115
namespace Schrijver
def upperRoots28 : List (Fin 3185) := [Tree28_000.root,Tree28_001.root,Tree28_002.root,Tree28_003.root,Tree28_004.root,Tree28_005.root,Tree28_006.root,Tree28_007.root,Tree28_008.root,Tree28_009.root,Tree28_010.root,Tree28_011.root,Tree28_012.root,Tree28_013.root,Tree28_014.root,Tree28_015.root,Tree28_016.root,Tree28_017.root,Tree28_018.root,Tree28_019.root,Tree28_020.root,Tree28_021.root,Tree28_022.root,Tree28_023.root,Tree28_024.root,Tree28_025.root,Tree28_026.root,Tree28_027.root,Tree28_028.root,Tree28_029.root,Tree28_030.root,Tree28_031.root,Tree28_032.root,Tree28_033.root,Tree28_034.root,Tree28_035.root,Tree28_036.root,Tree28_037.root,Tree28_038.root,Tree28_039.root,Tree28_040.root,Tree28_041.root,Tree28_042.root,Tree28_043.root,Tree28_044.root,Tree28_045.root,Tree28_046.root,Tree28_047.root,Tree28_048.root,Tree28_049.root,Tree28_050.root,Tree28_051.root,Tree28_052.root,Tree28_053.root,Tree28_054.root,Tree28_055.root,Tree28_056.root,Tree28_057.root,Tree28_058.root,Tree28_059.root,Tree28_060.root,Tree28_061.root,Tree28_062.root,Tree28_063.root,Tree28_064.root,Tree28_065.root,Tree28_066.root,Tree28_067.root,Tree28_068.root,Tree28_069.root,Tree28_070.root,Tree28_071.root,Tree28_072.root,Tree28_073.root,Tree28_074.root,Tree28_075.root,Tree28_076.root,Tree28_077.root,Tree28_078.root,Tree28_079.root,Tree28_080.root,Tree28_081.root,Tree28_082.root,Tree28_083.root,Tree28_084.root,Tree28_085.root,Tree28_086.root,Tree28_087.root,Tree28_088.root,Tree28_089.root,Tree28_090.root,Tree28_091.root,Tree28_092.root,Tree28_093.root,Tree28_094.root,Tree28_095.root,Tree28_096.root,Tree28_097.root,Tree28_098.root,Tree28_099.root,Tree28_100.root,Tree28_101.root,Tree28_102.root,Tree28_103.root,Tree28_104.root,Tree28_105.root,Tree28_106.root,Tree28_107.root,Tree28_108.root,Tree28_109.root,Tree28_110.root,Tree28_111.root,Tree28_112.root,Tree28_113.root,Tree28_114.root,Tree28_115.root]
theorem upperTrees28 (r : Fin 3185) (hr : r ∈ upperRoots28) (v : Fin 3185) :
    ∃ p : (indexedGraph 3185 maskAt28).Walk v r, p.length ≤ 6 := by
  simp only [upperRoots28, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨p, hp⟩ := Tree28_000.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_001.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_002.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_003.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_004.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_005.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_006.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_007.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_008.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_009.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_010.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_011.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_012.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_013.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_014.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_015.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_016.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_017.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_018.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_019.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_020.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_021.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_022.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_023.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_024.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_025.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_026.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_027.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_028.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_029.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_030.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_031.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_032.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_033.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_034.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_035.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_036.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_037.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_038.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_039.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_040.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_041.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_042.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_043.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_044.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_045.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_046.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_047.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_048.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_049.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_050.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_051.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_052.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_053.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_054.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_055.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_056.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_057.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_058.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_059.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_060.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_061.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_062.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_063.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_064.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_065.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_066.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_067.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_068.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_069.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_070.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_071.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_072.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_073.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_074.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_075.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_076.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_077.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_078.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_079.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_080.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_081.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_082.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_083.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_084.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_085.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_086.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_087.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_088.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_089.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_090.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_091.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_092.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_093.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_094.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_095.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_096.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_097.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_098.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_099.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_100.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_101.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_102.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_103.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_104.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_105.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_106.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_107.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_108.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_109.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_110.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_111.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_112.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_113.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_114.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
  · obtain ⟨p, hp⟩ := Tree28_115.sound.2 v
    exact ⟨p, hp.trans (by decide)⟩
end Schrijver
