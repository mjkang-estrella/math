import Closure541
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2168 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2168 : ∀ h, Pure node2168 h → 11 ≤ h.length := by
  apply indexed_extend node2168 [(1, node1133), (3, node1710), (7, node1706), (10, node1699), (12, node1698), (13, node1743), (14, node1695)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1133
  · exact lower1710
  · exact lower1706
  · exact lower1699
  · exact lower1698
  · exact lower1743
  · exact lower1695
def node2169 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2169 : ∀ h, Pure node2169 h → 11 ≤ h.length := by
  apply indexed_extend node2169 [(1, node1134), (3, node1711), (8, node1707), (10, node1703), (12, node1700), (13, node1744)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1134
  · exact lower1711
  · exact lower1707
  · exact lower1703
  · exact lower1700
  · exact lower1744
def node2170 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 2], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2170 : ∀ h, Pure node2170 h → 11 ≤ h.length := by
  apply indexed_extend node2170 [(1, node1135), (3, node1712), (6, node1706), (10, node1704), (12, node1701), (13, node1745), (14, node1696)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1135
  · exact lower1712
  · exact lower1706
  · exact lower1704
  · exact lower1701
  · exact lower1745
  · exact lower1696
def node2171 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2171 : ∀ h, Pure node2171 h → 11 ≤ h.length := by
  apply indexed_extend node2171 [(1, node1136), (3, node1713), (7, node1707), (10, node1705), (12, node1702), (13, node1746), (14, node1697)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1136
  · exact lower1713
  · exact lower1707
  · exact lower1705
  · exact lower1702
  · exact lower1746
  · exact lower1697
def entries542 : List Graph := [node2168, node2169, node2170, node2171]
theorem entries_count542 : entries542.length = 4 := by decide +kernel
theorem census_node2168 : ((verts node2168).filter (wye node2168)).length = 7 := by decide +kernel
theorem census_node2169 : ((verts node2169).filter (wye node2169)).length = 6 := by decide +kernel
theorem census_node2170 : ((verts node2170).filter (wye node2170)).length = 7 := by decide +kernel
theorem census_node2171 : ((verts node2171).filter (wye node2171)).length = 7 := by decide +kernel
theorem arc_count542 : (entries542.map (fun g => ((verts g).filter (wye g)).length)).sum = 27 := by
  simp only [entries542, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node2168, census_node2169, census_node2170, census_node2171]
  decide +kernel
end RawCert
