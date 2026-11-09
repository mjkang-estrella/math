import Closure514
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2060 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2060 : ∀ h, Pure node2060 h → 11 ≤ h.length := by
  apply indexed_extend node2060 [(0, node1134), (2, node1060), (3, node1523), (5, node1572), (8, node1487), (10, node1481), (11, node1615), (12, node1459)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1134
  · exact lower1060
  · exact lower1523
  · exact lower1572
  · exact lower1487
  · exact lower1481
  · exact lower1615
  · exact lower1459
def node2061 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 2], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2061 : ∀ h, Pure node2061 h → 11 ≤ h.length := by
  apply indexed_extend node2061 [(0, node1135), (2, node1061), (3, node1524), (5, node1573), (6, node1484), (10, node1482), (12, node1460), (14, node1456)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1135
  · exact lower1061
  · exact lower1524
  · exact lower1573
  · exact lower1484
  · exact lower1482
  · exact lower1460
  · exact lower1456
def node2062 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2062 : ∀ h, Pure node2062 h → 11 ≤ h.length := by
  apply indexed_extend node2062 [(0, node1136), (2, node1062), (3, node1525), (7, node1487), (10, node1483), (11, node1605), (12, node1461), (14, node1457)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1136
  · exact lower1062
  · exact lower1525
  · exact lower1487
  · exact lower1483
  · exact lower1605
  · exact lower1461
  · exact lower1457
def node2063 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower2063 : ∀ h, Pure node2063 h → 11 ≤ h.length := by
  apply indexed_extend node2063 [(0, node1143), (2, node1063), (3, node1526), (5, node1561), (6, node1489), (10, node1485), (12, node1464)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1143
  · exact lower1063
  · exact lower1526
  · exact lower1561
  · exact lower1489
  · exact lower1485
  · exact lower1464
def entries515 : List Graph := [node2060, node2061, node2062, node2063]
theorem entries_count515 : entries515.length = 4 := by decide +kernel
theorem census_node2060 : ((verts node2060).filter (wye node2060)).length = 8 := by decide +kernel
theorem census_node2061 : ((verts node2061).filter (wye node2061)).length = 8 := by decide +kernel
theorem census_node2062 : ((verts node2062).filter (wye node2062)).length = 8 := by decide +kernel
theorem census_node2063 : ((verts node2063).filter (wye node2063)).length = 7 := by decide +kernel
theorem arc_count515 : (entries515.map (fun g => ((verts g).filter (wye g)).length)).sum = 31 := by
  simp only [entries515, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node2060, census_node2061, census_node2062, census_node2063]
  decide +kernel
end RawCert
