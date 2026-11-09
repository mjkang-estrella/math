import Closure288
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1156 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1156 : ∀ h, Pure node1156 h → 11 ≤ h.length := by
  apply indexed_extend node1156 [(3, node297), (8, node460), (9, node459)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower297
  · exact lower460
  · exact lower459
def node1157 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0], [0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower1157 : ∀ h, Pure node1157 h → 11 ≤ h.length := by
  apply indexed_extend node1157 [(0, node925), (3, node300), (5, node467), (6, node502), (7, node461)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower925
  · exact lower300
  · exact lower467
  · exact lower502
  · exact lower461
def node1158 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower1158 : ∀ h, Pure node1158 h → 11 ≤ h.length := by
  apply indexed_extend node1158 [(0, node926), (3, node301), (5, node468), (12, node560)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower926
  · exact lower301
  · exact lower468
  · exact lower560
def node1159 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 0, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [0, 0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0], [0, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0]]
theorem lower1159 : ∀ h, Pure node1159 h → 11 ≤ h.length := by
  apply indexed_extend node1159 [(0, node932), (5, node469), (6, node504), (9, node461), (12, node564)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower932
  · exact lower469
  · exact lower504
  · exact lower461
  · exact lower564
def entries289 : List Graph := [node1156, node1157, node1158, node1159]
theorem entries_count289 : entries289.length = 4 := by decide +kernel
theorem census_node1156 : ((verts node1156).filter (wye node1156)).length = 3 := by decide +kernel
theorem census_node1157 : ((verts node1157).filter (wye node1157)).length = 5 := by decide +kernel
theorem census_node1158 : ((verts node1158).filter (wye node1158)).length = 4 := by decide +kernel
theorem census_node1159 : ((verts node1159).filter (wye node1159)).length = 5 := by decide +kernel
theorem arc_count289 : (entries289.map (fun g => ((verts g).filter (wye g)).length)).sum = 17 := by
  simp only [entries289, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1156, census_node1157, census_node1158, census_node1159]
  decide +kernel
end RawCert
