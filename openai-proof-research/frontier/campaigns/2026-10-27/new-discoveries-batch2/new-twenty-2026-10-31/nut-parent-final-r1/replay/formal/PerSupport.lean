import FiniteSupport000
import FiniteSupport001
import FiniteSupport002
import FiniteSupport003
import FiniteSupport004
import FiniteSupport005
import FiniteSupport006
import FiniteSupport007
import FiniteSupport008
import FiniteSupport009
import FiniteSupport010
import FiniteSupport011
import FiniteSupport012
import FiniteSupport013
import FiniteSupport014
import FiniteSupport015
import FiniteSupport016
import FiniteSupport017
import FiniteSupport018
import FiniteSupport019
import FiniteSupport020
import FiniteSupport021
import FiniteSupport022
import FiniteSupport023
import FiniteSupport024
import FiniteSupport025
import FiniteSupport026
import FiniteSupport027
import FiniteSupport028
import FiniteSupport029
import FiniteSupport030
import FiniteSupport031
import FiniteSupport032
import FiniteSupport033
import FiniteSupport034
import FiniteSupport035
import FiniteSupport036
import FiniteSupport037
import FiniteSupport038
import FiniteSupport039
import FiniteSupport040
import FiniteSupport041
import FiniteSupport042
import FiniteSupport043
import FiniteSupport044
import FiniteSupport045
import FiniteSupport046
import FiniteSupport047
import FiniteSupport048
import FiniteSupport049
import FiniteSupport050
import FiniteSupport051
import FiniteSupport052
import FiniteSupport053
import FiniteSupport054
import FiniteSupport055
import FiniteSupport056
import FiniteSupport057
import FiniteSupport058
import FiniteSupport059
import FiniteSupport060
import FiniteSupport061
import FiniteSupport062
import FiniteSupport063
import FiniteSupport064
import FiniteSupport065
import FiniteSupport066
import FiniteSupport067
import FiniteSupport068
import FiniteSupport069
import FiniteSupport070
import FiniteSupport071
import FiniteSupport072
import FiniteSupport073
import FiniteSupport074
import FiniteSupport075
import FiniteSupport076
import FiniteSupport077
import FiniteSupport078
import FiniteSupport079
import FiniteSupport080
import FiniteSupport081
import FiniteSupport082
import FiniteSupport083
import FiniteSupport084
import FiniteSupport085
import FiniteSupport086
import FiniteSupport087
import FiniteSupport088
import FiniteSupport089
import FiniteSupport090
import FiniteSupport091
import FiniteSupport092
import FiniteSupport093
import FiniteSupport094
import FiniteSupport095
import FiniteSupport096
import FiniteSupport097
import FiniteSupport098
import FiniteSupport099
import FiniteSupport100
import FiniteSupport101
import FiniteSupport102
import FiniteSupport103
import FiniteSupport104
import FiniteSupport105
import FiniteSupport106
import FiniteSupport107
import FiniteSupport108
import FiniteSupport109
import FiniteSupport110
import FiniteSupport111
import FiniteSupport112
import FiniteSupport113
import FiniteSupport114
import FiniteSupport115
import FiniteSupport116
import FiniteSupport117
import FiniteSupport118
import FiniteSupport119
import FiniteSupport120
import FiniteSupport121
import FiniteSupport122
import FiniteSupport123
import FiniteSupport124
import FiniteSupport125
import FiniteSupport126
import FiniteSupport127
import FiniteSupport128
import FiniteSupport129
import FiniteSupport130
import FiniteSupport131
import FiniteSupport132
import FiniteSupport133
import FiniteSupport134
import FiniteSupport135
import FiniteSupport136
import FiniteSupport137
import FiniteSupport138
import FiniteSupport139
import FiniteSupport140
import FiniteSupport141
import FiniteSupport142
import FiniteSupport143
import FiniteSupport144
import FiniteSupport145
import FiniteSupport146
import FiniteSupport147
import FiniteSupport148
import FiniteSupport149
import FiniteSupport150
import FiniteSupport151
import FiniteSupport152
import FiniteSupport153
import FiniteSupport154
import FiniteSupport155
import FiniteSupport156
import FiniteSupport157
import FiniteSupport158
import FiniteSupport159
import FiniteSupport160
import FiniteSupport161
import FiniteSupport162
import FiniteSupport163
import FiniteSupport164
import FiniteSupport165
import FiniteSupport166
import FiniteSupport167
import FiniteSupport168
import FiniteSupport169
import FiniteSupport170
import FiniteSupport171
import FiniteSupport172
import FiniteSupport173
import FiniteSupport174
import FiniteSupport175
import FiniteSupport176
import FiniteSupport177
import FiniteSupport178
import FiniteSupport179
import FiniteSupport180
import FiniteSupport181
import FiniteSupport182
import FiniteSupport183
import FiniteSupport184
import FiniteSupport185
import FiniteSupport186
import FiniteSupport187
import FiniteSupport188
import FiniteSupport189
import FiniteSupport190
import FiniteSupport191
import FiniteSupport192
import FiniteSupport193
set_option maxRecDepth 4096
namespace Nut8
theorem per_support : PerSupport := by
  apply per_support_of_signed_catalogues
  intro code hc
  simp only [GraphClosure7_000.targets, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨FiniteSupport000.e, FiniteSupport000.p, FiniteSupport000.tree, FiniteSupport000.verified⟩
  · exact ⟨FiniteSupport001.e, FiniteSupport001.p, FiniteSupport001.tree, FiniteSupport001.verified⟩
  · exact ⟨FiniteSupport002.e, FiniteSupport002.p, FiniteSupport002.tree, FiniteSupport002.verified⟩
  · exact ⟨FiniteSupport003.e, FiniteSupport003.p, FiniteSupport003.tree, FiniteSupport003.verified⟩
  · exact ⟨FiniteSupport004.e, FiniteSupport004.p, FiniteSupport004.tree, FiniteSupport004.verified⟩
  · exact ⟨FiniteSupport005.e, FiniteSupport005.p, FiniteSupport005.tree, FiniteSupport005.verified⟩
  · exact ⟨FiniteSupport006.e, FiniteSupport006.p, FiniteSupport006.tree, FiniteSupport006.verified⟩
  · exact ⟨FiniteSupport007.e, FiniteSupport007.p, FiniteSupport007.tree, FiniteSupport007.verified⟩
  · exact ⟨FiniteSupport008.e, FiniteSupport008.p, FiniteSupport008.tree, FiniteSupport008.verified⟩
  · exact ⟨FiniteSupport009.e, FiniteSupport009.p, FiniteSupport009.tree, FiniteSupport009.verified⟩
  · exact ⟨FiniteSupport010.e, FiniteSupport010.p, FiniteSupport010.tree, FiniteSupport010.verified⟩
  · exact ⟨FiniteSupport011.e, FiniteSupport011.p, FiniteSupport011.tree, FiniteSupport011.verified⟩
  · exact ⟨FiniteSupport012.e, FiniteSupport012.p, FiniteSupport012.tree, FiniteSupport012.verified⟩
  · exact ⟨FiniteSupport013.e, FiniteSupport013.p, FiniteSupport013.tree, FiniteSupport013.verified⟩
  · exact ⟨FiniteSupport014.e, FiniteSupport014.p, FiniteSupport014.tree, FiniteSupport014.verified⟩
  · exact ⟨FiniteSupport015.e, FiniteSupport015.p, FiniteSupport015.tree, FiniteSupport015.verified⟩
  · exact ⟨FiniteSupport016.e, FiniteSupport016.p, FiniteSupport016.tree, FiniteSupport016.verified⟩
  · exact ⟨FiniteSupport017.e, FiniteSupport017.p, FiniteSupport017.tree, FiniteSupport017.verified⟩
  · exact ⟨FiniteSupport018.e, FiniteSupport018.p, FiniteSupport018.tree, FiniteSupport018.verified⟩
  · exact ⟨FiniteSupport019.e, FiniteSupport019.p, FiniteSupport019.tree, FiniteSupport019.verified⟩
  · exact ⟨FiniteSupport020.e, FiniteSupport020.p, FiniteSupport020.tree, FiniteSupport020.verified⟩
  · exact ⟨FiniteSupport021.e, FiniteSupport021.p, FiniteSupport021.tree, FiniteSupport021.verified⟩
  · exact ⟨FiniteSupport022.e, FiniteSupport022.p, FiniteSupport022.tree, FiniteSupport022.verified⟩
  · exact ⟨FiniteSupport023.e, FiniteSupport023.p, FiniteSupport023.tree, FiniteSupport023.verified⟩
  · exact ⟨FiniteSupport024.e, FiniteSupport024.p, FiniteSupport024.tree, FiniteSupport024.verified⟩
  · exact ⟨FiniteSupport025.e, FiniteSupport025.p, FiniteSupport025.tree, FiniteSupport025.verified⟩
  · exact ⟨FiniteSupport026.e, FiniteSupport026.p, FiniteSupport026.tree, FiniteSupport026.verified⟩
  · exact ⟨FiniteSupport027.e, FiniteSupport027.p, FiniteSupport027.tree, FiniteSupport027.verified⟩
  · exact ⟨FiniteSupport028.e, FiniteSupport028.p, FiniteSupport028.tree, FiniteSupport028.verified⟩
  · exact ⟨FiniteSupport029.e, FiniteSupport029.p, FiniteSupport029.tree, FiniteSupport029.verified⟩
  · exact ⟨FiniteSupport030.e, FiniteSupport030.p, FiniteSupport030.tree, FiniteSupport030.verified⟩
  · exact ⟨FiniteSupport031.e, FiniteSupport031.p, FiniteSupport031.tree, FiniteSupport031.verified⟩
  · exact ⟨FiniteSupport032.e, FiniteSupport032.p, FiniteSupport032.tree, FiniteSupport032.verified⟩
  · exact ⟨FiniteSupport033.e, FiniteSupport033.p, FiniteSupport033.tree, FiniteSupport033.verified⟩
  · exact ⟨FiniteSupport034.e, FiniteSupport034.p, FiniteSupport034.tree, FiniteSupport034.verified⟩
  · exact ⟨FiniteSupport035.e, FiniteSupport035.p, FiniteSupport035.tree, FiniteSupport035.verified⟩
  · exact ⟨FiniteSupport036.e, FiniteSupport036.p, FiniteSupport036.tree, FiniteSupport036.verified⟩
  · exact ⟨FiniteSupport037.e, FiniteSupport037.p, FiniteSupport037.tree, FiniteSupport037.verified⟩
  · exact ⟨FiniteSupport038.e, FiniteSupport038.p, FiniteSupport038.tree, FiniteSupport038.verified⟩
  · exact ⟨FiniteSupport039.e, FiniteSupport039.p, FiniteSupport039.tree, FiniteSupport039.verified⟩
  · exact ⟨FiniteSupport040.e, FiniteSupport040.p, FiniteSupport040.tree, FiniteSupport040.verified⟩
  · exact ⟨FiniteSupport041.e, FiniteSupport041.p, FiniteSupport041.tree, FiniteSupport041.verified⟩
  · exact ⟨FiniteSupport042.e, FiniteSupport042.p, FiniteSupport042.tree, FiniteSupport042.verified⟩
  · exact ⟨FiniteSupport043.e, FiniteSupport043.p, FiniteSupport043.tree, FiniteSupport043.verified⟩
  · exact ⟨FiniteSupport044.e, FiniteSupport044.p, FiniteSupport044.tree, FiniteSupport044.verified⟩
  · exact ⟨FiniteSupport045.e, FiniteSupport045.p, FiniteSupport045.tree, FiniteSupport045.verified⟩
  · exact ⟨FiniteSupport046.e, FiniteSupport046.p, FiniteSupport046.tree, FiniteSupport046.verified⟩
  · exact ⟨FiniteSupport047.e, FiniteSupport047.p, FiniteSupport047.tree, FiniteSupport047.verified⟩
  · exact ⟨FiniteSupport048.e, FiniteSupport048.p, FiniteSupport048.tree, FiniteSupport048.verified⟩
  · exact ⟨FiniteSupport049.e, FiniteSupport049.p, FiniteSupport049.tree, FiniteSupport049.verified⟩
  · exact ⟨FiniteSupport050.e, FiniteSupport050.p, FiniteSupport050.tree, FiniteSupport050.verified⟩
  · exact ⟨FiniteSupport051.e, FiniteSupport051.p, FiniteSupport051.tree, FiniteSupport051.verified⟩
  · exact ⟨FiniteSupport052.e, FiniteSupport052.p, FiniteSupport052.tree, FiniteSupport052.verified⟩
  · exact ⟨FiniteSupport053.e, FiniteSupport053.p, FiniteSupport053.tree, FiniteSupport053.verified⟩
  · exact ⟨FiniteSupport054.e, FiniteSupport054.p, FiniteSupport054.tree, FiniteSupport054.verified⟩
  · exact ⟨FiniteSupport055.e, FiniteSupport055.p, FiniteSupport055.tree, FiniteSupport055.verified⟩
  · exact ⟨FiniteSupport056.e, FiniteSupport056.p, FiniteSupport056.tree, FiniteSupport056.verified⟩
  · exact ⟨FiniteSupport057.e, FiniteSupport057.p, FiniteSupport057.tree, FiniteSupport057.verified⟩
  · exact ⟨FiniteSupport058.e, FiniteSupport058.p, FiniteSupport058.tree, FiniteSupport058.verified⟩
  · exact ⟨FiniteSupport059.e, FiniteSupport059.p, FiniteSupport059.tree, FiniteSupport059.verified⟩
  · exact ⟨FiniteSupport060.e, FiniteSupport060.p, FiniteSupport060.tree, FiniteSupport060.verified⟩
  · exact ⟨FiniteSupport061.e, FiniteSupport061.p, FiniteSupport061.tree, FiniteSupport061.verified⟩
  · exact ⟨FiniteSupport062.e, FiniteSupport062.p, FiniteSupport062.tree, FiniteSupport062.verified⟩
  · exact ⟨FiniteSupport063.e, FiniteSupport063.p, FiniteSupport063.tree, FiniteSupport063.verified⟩
  · exact ⟨FiniteSupport064.e, FiniteSupport064.p, FiniteSupport064.tree, FiniteSupport064.verified⟩
  · exact ⟨FiniteSupport065.e, FiniteSupport065.p, FiniteSupport065.tree, FiniteSupport065.verified⟩
  · exact ⟨FiniteSupport066.e, FiniteSupport066.p, FiniteSupport066.tree, FiniteSupport066.verified⟩
  · exact ⟨FiniteSupport067.e, FiniteSupport067.p, FiniteSupport067.tree, FiniteSupport067.verified⟩
  · exact ⟨FiniteSupport068.e, FiniteSupport068.p, FiniteSupport068.tree, FiniteSupport068.verified⟩
  · exact ⟨FiniteSupport069.e, FiniteSupport069.p, FiniteSupport069.tree, FiniteSupport069.verified⟩
  · exact ⟨FiniteSupport070.e, FiniteSupport070.p, FiniteSupport070.tree, FiniteSupport070.verified⟩
  · exact ⟨FiniteSupport071.e, FiniteSupport071.p, FiniteSupport071.tree, FiniteSupport071.verified⟩
  · exact ⟨FiniteSupport072.e, FiniteSupport072.p, FiniteSupport072.tree, FiniteSupport072.verified⟩
  · exact ⟨FiniteSupport073.e, FiniteSupport073.p, FiniteSupport073.tree, FiniteSupport073.verified⟩
  · exact ⟨FiniteSupport074.e, FiniteSupport074.p, FiniteSupport074.tree, FiniteSupport074.verified⟩
  · exact ⟨FiniteSupport075.e, FiniteSupport075.p, FiniteSupport075.tree, FiniteSupport075.verified⟩
  · exact ⟨FiniteSupport076.e, FiniteSupport076.p, FiniteSupport076.tree, FiniteSupport076.verified⟩
  · exact ⟨FiniteSupport077.e, FiniteSupport077.p, FiniteSupport077.tree, FiniteSupport077.verified⟩
  · exact ⟨FiniteSupport078.e, FiniteSupport078.p, FiniteSupport078.tree, FiniteSupport078.verified⟩
  · exact ⟨FiniteSupport079.e, FiniteSupport079.p, FiniteSupport079.tree, FiniteSupport079.verified⟩
  · exact ⟨FiniteSupport080.e, FiniteSupport080.p, FiniteSupport080.tree, FiniteSupport080.verified⟩
  · exact ⟨FiniteSupport081.e, FiniteSupport081.p, FiniteSupport081.tree, FiniteSupport081.verified⟩
  · exact ⟨FiniteSupport082.e, FiniteSupport082.p, FiniteSupport082.tree, FiniteSupport082.verified⟩
  · exact ⟨FiniteSupport083.e, FiniteSupport083.p, FiniteSupport083.tree, FiniteSupport083.verified⟩
  · exact ⟨FiniteSupport084.e, FiniteSupport084.p, FiniteSupport084.tree, FiniteSupport084.verified⟩
  · exact ⟨FiniteSupport085.e, FiniteSupport085.p, FiniteSupport085.tree, FiniteSupport085.verified⟩
  · exact ⟨FiniteSupport086.e, FiniteSupport086.p, FiniteSupport086.tree, FiniteSupport086.verified⟩
  · exact ⟨FiniteSupport087.e, FiniteSupport087.p, FiniteSupport087.tree, FiniteSupport087.verified⟩
  · exact ⟨FiniteSupport088.e, FiniteSupport088.p, FiniteSupport088.tree, FiniteSupport088.verified⟩
  · exact ⟨FiniteSupport089.e, FiniteSupport089.p, FiniteSupport089.tree, FiniteSupport089.verified⟩
  · exact ⟨FiniteSupport090.e, FiniteSupport090.p, FiniteSupport090.tree, FiniteSupport090.verified⟩
  · exact ⟨FiniteSupport091.e, FiniteSupport091.p, FiniteSupport091.tree, FiniteSupport091.verified⟩
  · exact ⟨FiniteSupport092.e, FiniteSupport092.p, FiniteSupport092.tree, FiniteSupport092.verified⟩
  · exact ⟨FiniteSupport093.e, FiniteSupport093.p, FiniteSupport093.tree, FiniteSupport093.verified⟩
  · exact ⟨FiniteSupport094.e, FiniteSupport094.p, FiniteSupport094.tree, FiniteSupport094.verified⟩
  · exact ⟨FiniteSupport095.e, FiniteSupport095.p, FiniteSupport095.tree, FiniteSupport095.verified⟩
  · exact ⟨FiniteSupport096.e, FiniteSupport096.p, FiniteSupport096.tree, FiniteSupport096.verified⟩
  · exact ⟨FiniteSupport097.e, FiniteSupport097.p, FiniteSupport097.tree, FiniteSupport097.verified⟩
  · exact ⟨FiniteSupport098.e, FiniteSupport098.p, FiniteSupport098.tree, FiniteSupport098.verified⟩
  · exact ⟨FiniteSupport099.e, FiniteSupport099.p, FiniteSupport099.tree, FiniteSupport099.verified⟩
  · exact ⟨FiniteSupport100.e, FiniteSupport100.p, FiniteSupport100.tree, FiniteSupport100.verified⟩
  · exact ⟨FiniteSupport101.e, FiniteSupport101.p, FiniteSupport101.tree, FiniteSupport101.verified⟩
  · exact ⟨FiniteSupport102.e, FiniteSupport102.p, FiniteSupport102.tree, FiniteSupport102.verified⟩
  · exact ⟨FiniteSupport103.e, FiniteSupport103.p, FiniteSupport103.tree, FiniteSupport103.verified⟩
  · exact ⟨FiniteSupport104.e, FiniteSupport104.p, FiniteSupport104.tree, FiniteSupport104.verified⟩
  · exact ⟨FiniteSupport105.e, FiniteSupport105.p, FiniteSupport105.tree, FiniteSupport105.verified⟩
  · exact ⟨FiniteSupport106.e, FiniteSupport106.p, FiniteSupport106.tree, FiniteSupport106.verified⟩
  · exact ⟨FiniteSupport107.e, FiniteSupport107.p, FiniteSupport107.tree, FiniteSupport107.verified⟩
  · exact ⟨FiniteSupport108.e, FiniteSupport108.p, FiniteSupport108.tree, FiniteSupport108.verified⟩
  · exact ⟨FiniteSupport109.e, FiniteSupport109.p, FiniteSupport109.tree, FiniteSupport109.verified⟩
  · exact ⟨FiniteSupport110.e, FiniteSupport110.p, FiniteSupport110.tree, FiniteSupport110.verified⟩
  · exact ⟨FiniteSupport111.e, FiniteSupport111.p, FiniteSupport111.tree, FiniteSupport111.verified⟩
  · exact ⟨FiniteSupport112.e, FiniteSupport112.p, FiniteSupport112.tree, FiniteSupport112.verified⟩
  · exact ⟨FiniteSupport113.e, FiniteSupport113.p, FiniteSupport113.tree, FiniteSupport113.verified⟩
  · exact ⟨FiniteSupport114.e, FiniteSupport114.p, FiniteSupport114.tree, FiniteSupport114.verified⟩
  · exact ⟨FiniteSupport115.e, FiniteSupport115.p, FiniteSupport115.tree, FiniteSupport115.verified⟩
  · exact ⟨FiniteSupport116.e, FiniteSupport116.p, FiniteSupport116.tree, FiniteSupport116.verified⟩
  · exact ⟨FiniteSupport117.e, FiniteSupport117.p, FiniteSupport117.tree, FiniteSupport117.verified⟩
  · exact ⟨FiniteSupport118.e, FiniteSupport118.p, FiniteSupport118.tree, FiniteSupport118.verified⟩
  · exact ⟨FiniteSupport119.e, FiniteSupport119.p, FiniteSupport119.tree, FiniteSupport119.verified⟩
  · exact ⟨FiniteSupport120.e, FiniteSupport120.p, FiniteSupport120.tree, FiniteSupport120.verified⟩
  · exact ⟨FiniteSupport121.e, FiniteSupport121.p, FiniteSupport121.tree, FiniteSupport121.verified⟩
  · exact ⟨FiniteSupport122.e, FiniteSupport122.p, FiniteSupport122.tree, FiniteSupport122.verified⟩
  · exact ⟨FiniteSupport123.e, FiniteSupport123.p, FiniteSupport123.tree, FiniteSupport123.verified⟩
  · exact ⟨FiniteSupport124.e, FiniteSupport124.p, FiniteSupport124.tree, FiniteSupport124.verified⟩
  · exact ⟨FiniteSupport125.e, FiniteSupport125.p, FiniteSupport125.tree, FiniteSupport125.verified⟩
  · exact ⟨FiniteSupport126.e, FiniteSupport126.p, FiniteSupport126.tree, FiniteSupport126.verified⟩
  · exact ⟨FiniteSupport127.e, FiniteSupport127.p, FiniteSupport127.tree, FiniteSupport127.verified⟩
  · exact ⟨FiniteSupport128.e, FiniteSupport128.p, FiniteSupport128.tree, FiniteSupport128.verified⟩
  · exact ⟨FiniteSupport129.e, FiniteSupport129.p, FiniteSupport129.tree, FiniteSupport129.verified⟩
  · exact ⟨FiniteSupport130.e, FiniteSupport130.p, FiniteSupport130.tree, FiniteSupport130.verified⟩
  · exact ⟨FiniteSupport131.e, FiniteSupport131.p, FiniteSupport131.tree, FiniteSupport131.verified⟩
  · exact ⟨FiniteSupport132.e, FiniteSupport132.p, FiniteSupport132.tree, FiniteSupport132.verified⟩
  · exact ⟨FiniteSupport133.e, FiniteSupport133.p, FiniteSupport133.tree, FiniteSupport133.verified⟩
  · exact ⟨FiniteSupport134.e, FiniteSupport134.p, FiniteSupport134.tree, FiniteSupport134.verified⟩
  · exact ⟨FiniteSupport135.e, FiniteSupport135.p, FiniteSupport135.tree, FiniteSupport135.verified⟩
  · exact ⟨FiniteSupport136.e, FiniteSupport136.p, FiniteSupport136.tree, FiniteSupport136.verified⟩
  · exact ⟨FiniteSupport137.e, FiniteSupport137.p, FiniteSupport137.tree, FiniteSupport137.verified⟩
  · exact ⟨FiniteSupport138.e, FiniteSupport138.p, FiniteSupport138.tree, FiniteSupport138.verified⟩
  · exact ⟨FiniteSupport139.e, FiniteSupport139.p, FiniteSupport139.tree, FiniteSupport139.verified⟩
  · exact ⟨FiniteSupport140.e, FiniteSupport140.p, FiniteSupport140.tree, FiniteSupport140.verified⟩
  · exact ⟨FiniteSupport141.e, FiniteSupport141.p, FiniteSupport141.tree, FiniteSupport141.verified⟩
  · exact ⟨FiniteSupport142.e, FiniteSupport142.p, FiniteSupport142.tree, FiniteSupport142.verified⟩
  · exact ⟨FiniteSupport143.e, FiniteSupport143.p, FiniteSupport143.tree, FiniteSupport143.verified⟩
  · exact ⟨FiniteSupport144.e, FiniteSupport144.p, FiniteSupport144.tree, FiniteSupport144.verified⟩
  · exact ⟨FiniteSupport145.e, FiniteSupport145.p, FiniteSupport145.tree, FiniteSupport145.verified⟩
  · exact ⟨FiniteSupport146.e, FiniteSupport146.p, FiniteSupport146.tree, FiniteSupport146.verified⟩
  · exact ⟨FiniteSupport147.e, FiniteSupport147.p, FiniteSupport147.tree, FiniteSupport147.verified⟩
  · exact ⟨FiniteSupport148.e, FiniteSupport148.p, FiniteSupport148.tree, FiniteSupport148.verified⟩
  · exact ⟨FiniteSupport149.e, FiniteSupport149.p, FiniteSupport149.tree, FiniteSupport149.verified⟩
  · exact ⟨FiniteSupport150.e, FiniteSupport150.p, FiniteSupport150.tree, FiniteSupport150.verified⟩
  · exact ⟨FiniteSupport151.e, FiniteSupport151.p, FiniteSupport151.tree, FiniteSupport151.verified⟩
  · exact ⟨FiniteSupport152.e, FiniteSupport152.p, FiniteSupport152.tree, FiniteSupport152.verified⟩
  · exact ⟨FiniteSupport153.e, FiniteSupport153.p, FiniteSupport153.tree, FiniteSupport153.verified⟩
  · exact ⟨FiniteSupport154.e, FiniteSupport154.p, FiniteSupport154.tree, FiniteSupport154.verified⟩
  · exact ⟨FiniteSupport155.e, FiniteSupport155.p, FiniteSupport155.tree, FiniteSupport155.verified⟩
  · exact ⟨FiniteSupport156.e, FiniteSupport156.p, FiniteSupport156.tree, FiniteSupport156.verified⟩
  · exact ⟨FiniteSupport157.e, FiniteSupport157.p, FiniteSupport157.tree, FiniteSupport157.verified⟩
  · exact ⟨FiniteSupport158.e, FiniteSupport158.p, FiniteSupport158.tree, FiniteSupport158.verified⟩
  · exact ⟨FiniteSupport159.e, FiniteSupport159.p, FiniteSupport159.tree, FiniteSupport159.verified⟩
  · exact ⟨FiniteSupport160.e, FiniteSupport160.p, FiniteSupport160.tree, FiniteSupport160.verified⟩
  · exact ⟨FiniteSupport161.e, FiniteSupport161.p, FiniteSupport161.tree, FiniteSupport161.verified⟩
  · exact ⟨FiniteSupport162.e, FiniteSupport162.p, FiniteSupport162.tree, FiniteSupport162.verified⟩
  · exact ⟨FiniteSupport163.e, FiniteSupport163.p, FiniteSupport163.tree, FiniteSupport163.verified⟩
  · exact ⟨FiniteSupport164.e, FiniteSupport164.p, FiniteSupport164.tree, FiniteSupport164.verified⟩
  · exact ⟨FiniteSupport165.e, FiniteSupport165.p, FiniteSupport165.tree, FiniteSupport165.verified⟩
  · exact ⟨FiniteSupport166.e, FiniteSupport166.p, FiniteSupport166.tree, FiniteSupport166.verified⟩
  · exact ⟨FiniteSupport167.e, FiniteSupport167.p, FiniteSupport167.tree, FiniteSupport167.verified⟩
  · exact ⟨FiniteSupport168.e, FiniteSupport168.p, FiniteSupport168.tree, FiniteSupport168.verified⟩
  · exact ⟨FiniteSupport169.e, FiniteSupport169.p, FiniteSupport169.tree, FiniteSupport169.verified⟩
  · exact ⟨FiniteSupport170.e, FiniteSupport170.p, FiniteSupport170.tree, FiniteSupport170.verified⟩
  · exact ⟨FiniteSupport171.e, FiniteSupport171.p, FiniteSupport171.tree, FiniteSupport171.verified⟩
  · exact ⟨FiniteSupport172.e, FiniteSupport172.p, FiniteSupport172.tree, FiniteSupport172.verified⟩
  · exact ⟨FiniteSupport173.e, FiniteSupport173.p, FiniteSupport173.tree, FiniteSupport173.verified⟩
  · exact ⟨FiniteSupport174.e, FiniteSupport174.p, FiniteSupport174.tree, FiniteSupport174.verified⟩
  · exact ⟨FiniteSupport175.e, FiniteSupport175.p, FiniteSupport175.tree, FiniteSupport175.verified⟩
  · exact ⟨FiniteSupport176.e, FiniteSupport176.p, FiniteSupport176.tree, FiniteSupport176.verified⟩
  · exact ⟨FiniteSupport177.e, FiniteSupport177.p, FiniteSupport177.tree, FiniteSupport177.verified⟩
  · exact ⟨FiniteSupport178.e, FiniteSupport178.p, FiniteSupport178.tree, FiniteSupport178.verified⟩
  · exact ⟨FiniteSupport179.e, FiniteSupport179.p, FiniteSupport179.tree, FiniteSupport179.verified⟩
  · exact ⟨FiniteSupport180.e, FiniteSupport180.p, FiniteSupport180.tree, FiniteSupport180.verified⟩
  · exact ⟨FiniteSupport181.e, FiniteSupport181.p, FiniteSupport181.tree, FiniteSupport181.verified⟩
  · exact ⟨FiniteSupport182.e, FiniteSupport182.p, FiniteSupport182.tree, FiniteSupport182.verified⟩
  · exact ⟨FiniteSupport183.e, FiniteSupport183.p, FiniteSupport183.tree, FiniteSupport183.verified⟩
  · exact ⟨FiniteSupport184.e, FiniteSupport184.p, FiniteSupport184.tree, FiniteSupport184.verified⟩
  · exact ⟨FiniteSupport185.e, FiniteSupport185.p, FiniteSupport185.tree, FiniteSupport185.verified⟩
  · exact ⟨FiniteSupport186.e, FiniteSupport186.p, FiniteSupport186.tree, FiniteSupport186.verified⟩
  · exact ⟨FiniteSupport187.e, FiniteSupport187.p, FiniteSupport187.tree, FiniteSupport187.verified⟩
  · exact ⟨FiniteSupport188.e, FiniteSupport188.p, FiniteSupport188.tree, FiniteSupport188.verified⟩
  · exact ⟨FiniteSupport189.e, FiniteSupport189.p, FiniteSupport189.tree, FiniteSupport189.verified⟩
  · exact ⟨FiniteSupport190.e, FiniteSupport190.p, FiniteSupport190.tree, FiniteSupport190.verified⟩
  · exact ⟨FiniteSupport191.e, FiniteSupport191.p, FiniteSupport191.tree, FiniteSupport191.verified⟩
  · exact ⟨FiniteSupport192.e, FiniteSupport192.p, FiniteSupport192.tree, FiniteSupport192.verified⟩
  · exact ⟨FiniteSupport193.e, FiniteSupport193.p, FiniteSupport193.tree, FiniteSupport193.verified⟩
end Nut8
