import Closure526
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2108 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2108 : ∀ h, Pure node2108 h → 11 ≤ h.length := by
  apply indexed_extend node2108 [(4, node1568), (7, node1574), (9, node1564), (10, node1563), (11, node1645), (12, node1551), (14, node1550)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1568
  · exact lower1574
  · exact lower1564
  · exact lower1563
  · exact lower1645
  · exact lower1551
  · exact lower1550
def node2109 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2109 : ∀ h, Pure node2109 h → 11 ≤ h.length := by
  apply indexed_extend node2109 [(2, node1435), (4, node1569), (9, node1566), (10, node1565), (11, node1646), (12, node1552)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1435
  · exact lower1569
  · exact lower1566
  · exact lower1565
  · exact lower1646
  · exact lower1552
def node2110 : Graph := [[0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2110 : ∀ h, Pure node2110 h → 11 ≤ h.length := by
  apply indexed_extend node2110 [(0, node978), (2, node1532), (4, node1578), (5, node1579), (7, node1576), (8, node1577), (11, node1647), (14, node1575)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower978
  · exact lower1532
  · exact lower1578
  · exact lower1579
  · exact lower1576
  · exact lower1577
  · exact lower1647
  · exact lower1575
def node2111 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 1, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower2111 : ∀ h, Pure node2111 h → 11 ≤ h.length := by
  apply indexed_extend node2111 [(3, node1620), (5, node1633), (6, node1594), (8, node1602), (10, node1580), (11, node1581)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1620
  · exact lower1633
  · exact lower1594
  · exact lower1602
  · exact lower1580
  · exact lower1581
def entries527 : List Graph := [node2108, node2109, node2110, node2111]
theorem entries_count527 : entries527.length = 4 := by decide +kernel
theorem census_node2108 : ((verts node2108).filter (wye node2108)).length = 7 := by decide +kernel
theorem census_node2109 : ((verts node2109).filter (wye node2109)).length = 6 := by decide +kernel
theorem census_node2110 : ((verts node2110).filter (wye node2110)).length = 8 := by decide +kernel
theorem census_node2111 : ((verts node2111).filter (wye node2111)).length = 6 := by decide +kernel
theorem arc_count527 : (entries527.map (fun g => ((verts g).filter (wye g)).length)).sum = 27 := by
  simp only [entries527, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node2108, census_node2109, census_node2110, census_node2111]
  decide +kernel
end RawCert
