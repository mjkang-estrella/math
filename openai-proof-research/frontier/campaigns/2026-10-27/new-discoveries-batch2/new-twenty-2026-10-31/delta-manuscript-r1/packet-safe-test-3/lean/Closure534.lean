import Closure533
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2136 : Graph := [[0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower2136 : ∀ h, Pure node2136 h → 11 ≤ h.length := by
  apply indexed_extend node2136 [(0, node1142), (1, node1088), (4, node1662), (7, node1671), (8, node1702), (11, node1651), (13, node1717)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1142
  · exact lower1088
  · exact lower1662
  · exact lower1671
  · exact lower1702
  · exact lower1651
  · exact lower1717
def node2137 : Graph := [[0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower2137 : ∀ h, Pure node2137 h → 11 ≤ h.length := by
  apply indexed_extend node2137 [(0, node1143), (1, node1089), (3, node1675), (6, node1668), (8, node1704), (10, node1652), (12, node1650)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1143
  · exact lower1089
  · exact lower1675
  · exact lower1668
  · exact lower1704
  · exact lower1652
  · exact lower1650
def node2138 : Graph := [[0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 1, 2, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower2138 : ∀ h, Pure node2138 h → 11 ≤ h.length := by
  apply indexed_extend node2138 [(0, node1144), (1, node1090), (3, node1676), (7, node1672), (8, node1705), (10, node1653), (12, node1651)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1144
  · exact lower1090
  · exact lower1676
  · exact lower1672
  · exact lower1705
  · exact lower1653
  · exact lower1651
def node2139 : Graph := [[0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower2139 : ∀ h, Pure node2139 h → 11 ≤ h.length := by
  apply indexed_extend node2139 [(0, node1145), (1, node1091), (6, node1666), (7, node1673), (9, node1652), (10, node1653)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1145
  · exact lower1091
  · exact lower1666
  · exact lower1673
  · exact lower1652
  · exact lower1653
def entries534 : List Graph := [node2136, node2137, node2138, node2139]
theorem entries_count534 : entries534.length = 4 := by decide +kernel
theorem census_node2136 : ((verts node2136).filter (wye node2136)).length = 7 := by decide +kernel
theorem census_node2137 : ((verts node2137).filter (wye node2137)).length = 7 := by decide +kernel
theorem census_node2138 : ((verts node2138).filter (wye node2138)).length = 7 := by decide +kernel
theorem census_node2139 : ((verts node2139).filter (wye node2139)).length = 6 := by decide +kernel
theorem arc_count534 : (entries534.map (fun g => ((verts g).filter (wye g)).length)).sum = 27 := by
  simp only [entries534, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node2136, census_node2137, census_node2138, census_node2139]
  decide +kernel
end RawCert
