import Closure447
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1792 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1792 : ∀ h, Pure node1792 h → 11 ≤ h.length := by
  apply indexed_extend node1792 [(2, node1248), (4, node1429), (6, node1068), (8, node1063), (9, node1064), (10, node1065), (12, node1030)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1248
  · exact lower1429
  · exact lower1068
  · exact lower1063
  · exact lower1064
  · exact lower1065
  · exact lower1030
def node1793 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1793 : ∀ h, Pure node1793 h → 11 ≤ h.length := by
  apply indexed_extend node1793 [(2, node1249), (3, node1239), (4, node1434), (9, node1066), (10, node1063), (12, node1031), (14, node1027)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1249
  · exact lower1239
  · exact lower1434
  · exact lower1066
  · exact lower1063
  · exact lower1031
  · exact lower1027
def node1794 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1794 : ∀ h, Pure node1794 h → 11 ≤ h.length := by
  apply indexed_extend node1794 [(2, node1250), (3, node1240), (6, node1069), (9, node1067), (10, node1064), (12, node1032), (14, node1028)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1250
  · exact lower1240
  · exact lower1069
  · exact lower1067
  · exact lower1064
  · exact lower1032
  · exact lower1028
def node1795 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1795 : ∀ h, Pure node1795 h → 11 ≤ h.length := by
  apply indexed_extend node1795 [(3, node1241), (4, node1430), (6, node1070), (8, node1066), (9, node1067), (10, node1065), (14, node1029)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1241
  · exact lower1430
  · exact lower1070
  · exact lower1066
  · exact lower1067
  · exact lower1065
  · exact lower1029
def entries448 : List Graph := [node1792, node1793, node1794, node1795]
theorem entries_count448 : entries448.length = 4 := by decide +kernel
theorem census_node1792 : ((verts node1792).filter (wye node1792)).length = 7 := by decide +kernel
theorem census_node1793 : ((verts node1793).filter (wye node1793)).length = 7 := by decide +kernel
theorem census_node1794 : ((verts node1794).filter (wye node1794)).length = 7 := by decide +kernel
theorem census_node1795 : ((verts node1795).filter (wye node1795)).length = 7 := by decide +kernel
theorem arc_count448 : (entries448.map (fun g => ((verts g).filter (wye g)).length)).sum = 28 := by
  simp only [entries448, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1792, census_node1793, census_node1794, census_node1795]
  decide +kernel
end RawCert
