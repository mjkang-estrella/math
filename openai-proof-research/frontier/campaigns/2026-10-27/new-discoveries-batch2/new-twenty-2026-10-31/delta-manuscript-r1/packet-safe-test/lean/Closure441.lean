import Closure440
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1764 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1764 : ∀ h, Pure node1764 h → 11 ≤ h.length := by
  apply indexed_extend node1764 [(3, node1050), (5, node1116), (7, node1003), (8, node1004), (9, node1005), (13, node986), (14, node985)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1050
  · exact lower1116
  · exact lower1003
  · exact lower1004
  · exact lower1005
  · exact lower986
  · exact lower985
def node1765 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1765 : ∀ h, Pure node1765 h → 11 ≤ h.length := by
  apply indexed_extend node1765 [(1, node1063), (2, node1051), (3, node1073), (5, node1117), (8, node1012), (10, node1006), (12, node989)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1063
  · exact lower1051
  · exact lower1073
  · exact lower1117
  · exact lower1012
  · exact lower1006
  · exact lower989
def node1766 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1766 : ∀ h, Pure node1766 h → 11 ≤ h.length := by
  apply indexed_extend node1766 [(1, node1064), (2, node1052), (3, node1074), (7, node1008), (8, node1013), (10, node1007), (12, node990)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1064
  · exact lower1052
  · exact lower1074
  · exact lower1008
  · exact lower1013
  · exact lower1007
  · exact lower990
def node1767 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1767 : ∀ h, Pure node1767 h → 11 ≤ h.length := by
  apply indexed_extend node1767 [(1, node1065), (2, node1053), (5, node1108), (7, node1009), (9, node1006), (10, node1007)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1065
  · exact lower1053
  · exact lower1108
  · exact lower1009
  · exact lower1006
  · exact lower1007
def entries441 : List Graph := [node1764, node1765, node1766, node1767]
theorem entries_count441 : entries441.length = 4 := by decide +kernel
theorem census_node1764 : ((verts node1764).filter (wye node1764)).length = 7 := by decide +kernel
theorem census_node1765 : ((verts node1765).filter (wye node1765)).length = 7 := by decide +kernel
theorem census_node1766 : ((verts node1766).filter (wye node1766)).length = 7 := by decide +kernel
theorem census_node1767 : ((verts node1767).filter (wye node1767)).length = 6 := by decide +kernel
theorem arc_count441 : (entries441.map (fun g => ((verts g).filter (wye g)).length)).sum = 27 := by
  simp only [entries441, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1764, census_node1765, census_node1766, census_node1767]
  decide +kernel
end RawCert
