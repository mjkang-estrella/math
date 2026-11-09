import Closure293
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1176 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 1, 0, 1, 0]]
theorem lower1176 : ∀ h, Pure node1176 h → 11 ≤ h.length := by
  apply indexed_extend node1176 [(0, node910), (2, node704), (3, node311), (8, node466), (11, node563)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower910
  · exact lower704
  · exact lower311
  · exact lower466
  · exact lower563
def node1177 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1177 : ∀ h, Pure node1177 h → 11 ≤ h.length := by
  apply indexed_extend node1177 [(0, node911), (2, node705), (4, node478), (6, node548), (13, node462)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower911
  · exact lower705
  · exact lower478
  · exact lower548
  · exact lower462
def node1178 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2], [0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0]]
theorem lower1178 : ∀ h, Pure node1178 h → 11 ≤ h.length := by
  apply indexed_extend node1178 [(0, node912), (2, node706), (6, node549), (10, node465), (12, node463)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower912
  · exact lower706
  · exact lower549
  · exact lower465
  · exact lower463
def node1179 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2, 0, 0, 0]]
theorem lower1179 : ∀ h, Pure node1179 h → 11 ≤ h.length := by
  apply indexed_extend node1179 [(0, node914), (2, node707), (3, node312), (10, node466), (11, node572), (12, node464)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower914
  · exact lower707
  · exact lower312
  · exact lower466
  · exact lower572
  · exact lower464
def entries294 : List Graph := [node1176, node1177, node1178, node1179]
theorem entries_count294 : entries294.length = 4 := by decide +kernel
theorem census_node1176 : ((verts node1176).filter (wye node1176)).length = 5 := by decide +kernel
theorem census_node1177 : ((verts node1177).filter (wye node1177)).length = 5 := by decide +kernel
theorem census_node1178 : ((verts node1178).filter (wye node1178)).length = 5 := by decide +kernel
theorem census_node1179 : ((verts node1179).filter (wye node1179)).length = 6 := by decide +kernel
theorem arc_count294 : (entries294.map (fun g => ((verts g).filter (wye g)).length)).sum = 21 := by
  simp only [entries294, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1176, census_node1177, census_node1178, census_node1179]
  decide +kernel
end RawCert
