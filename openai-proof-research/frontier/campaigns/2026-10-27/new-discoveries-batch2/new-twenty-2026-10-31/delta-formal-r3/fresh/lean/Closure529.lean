import Closure528
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2116 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 1, 0], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1], [1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0]]
theorem lower2116 : ∀ h, Pure node2116 h → 11 ≤ h.length := by
  apply indexed_extend node2116 [(3, node1623), (4, node1616), (5, node1637), (6, node1606), (10, node1587), (11, node1588)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1623
  · exact lower1616
  · exact lower1637
  · exact lower1606
  · exact lower1587
  · exact lower1588
def node2117 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], [1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower2117 : ∀ h, Pure node2117 h → 11 ≤ h.length := by
  apply indexed_extend node2117 [(3, node1624), (5, node1638), (6, node1607), (7, node1610), (10, node1590), (11, node1592), (12, node1589)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1624
  · exact lower1638
  · exact lower1607
  · exact lower1610
  · exact lower1590
  · exact lower1592
  · exact lower1589
def node2118 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], [1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower2118 : ∀ h, Pure node2118 h → 11 ≤ h.length := by
  apply indexed_extend node2118 [(4, node1617), (5, node1639), (6, node1608), (7, node1611), (10, node1591), (12, node1589)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1617
  · exact lower1639
  · exact lower1608
  · exact lower1611
  · exact lower1591
  · exact lower1589
def node2119 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower2119 : ∀ h, Pure node2119 h → 11 ≤ h.length := by
  apply indexed_extend node2119 [(3, node1625), (4, node1618), (7, node1612), (10, node1593), (11, node1590), (12, node1591), (14, node1587)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1625
  · exact lower1618
  · exact lower1612
  · exact lower1593
  · exact lower1590
  · exact lower1591
  · exact lower1587
def entries529 : List Graph := [node2116, node2117, node2118, node2119]
theorem entries_count529 : entries529.length = 4 := by decide +kernel
theorem census_node2116 : ((verts node2116).filter (wye node2116)).length = 6 := by decide +kernel
theorem census_node2117 : ((verts node2117).filter (wye node2117)).length = 7 := by decide +kernel
theorem census_node2118 : ((verts node2118).filter (wye node2118)).length = 6 := by decide +kernel
theorem census_node2119 : ((verts node2119).filter (wye node2119)).length = 7 := by decide +kernel
theorem arc_count529 : (entries529.map (fun g => ((verts g).filter (wye g)).length)).sum = 26 := by
  simp only [entries529, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node2116, census_node2117, census_node2118, census_node2119]
  decide +kernel
end RawCert
