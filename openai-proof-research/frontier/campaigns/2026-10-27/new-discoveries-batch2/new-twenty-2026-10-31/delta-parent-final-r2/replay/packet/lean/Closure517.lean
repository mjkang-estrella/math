import Closure516
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2068 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0]]
theorem lower2068 : ∀ h, Pure node2068 h → 11 ≤ h.length := by
  apply indexed_extend node2068 [(0, node1150), (3, node1528), (5, node1563), (8, node1489), (10, node1488), (11, node1607), (12, node1468)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1150
  · exact lower1528
  · exact lower1563
  · exact lower1489
  · exact lower1488
  · exact lower1607
  · exact lower1468
def node2069 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2069 : ∀ h, Pure node2069 h → 11 ≤ h.length := by
  apply indexed_extend node2069 [(0, node1151), (4, node1511), (5, node1564), (8, node1490), (10, node1488), (11, node1609), (14, node1466)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1151
  · exact lower1511
  · exact lower1564
  · exact lower1490
  · exact lower1488
  · exact lower1609
  · exact lower1466
def node2070 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2070 : ∀ h, Pure node2070 h → 11 ≤ h.length := by
  apply indexed_extend node2070 [(0, node1152), (3, node1529), (4, node1512), (5, node1574), (9, node1490), (10, node1489), (12, node1469), (14, node1467)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1152
  · exact lower1529
  · exact lower1512
  · exact lower1574
  · exact lower1490
  · exact lower1489
  · exact lower1469
  · exact lower1467
def node2071 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower2071 : ∀ h, Pure node2071 h → 11 ≤ h.length := by
  apply indexed_extend node2071 [(0, node1154), (2, node1068), (3, node1530), (5, node1565), (9, node1491), (10, node1492), (11, node1610), (12, node1470)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1154
  · exact lower1068
  · exact lower1530
  · exact lower1565
  · exact lower1491
  · exact lower1492
  · exact lower1610
  · exact lower1470
def entries517 : List Graph := [node2068, node2069, node2070, node2071]
theorem entries_count517 : entries517.length = 4 := by decide +kernel
theorem census_node2068 : ((verts node2068).filter (wye node2068)).length = 7 := by decide +kernel
theorem census_node2069 : ((verts node2069).filter (wye node2069)).length = 7 := by decide +kernel
theorem census_node2070 : ((verts node2070).filter (wye node2070)).length = 8 := by decide +kernel
theorem census_node2071 : ((verts node2071).filter (wye node2071)).length = 8 := by decide +kernel
theorem arc_count517 : (entries517.map (fun g => ((verts g).filter (wye g)).length)).sum = 30 := by
  simp only [entries517, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node2068, census_node2069, census_node2070, census_node2071]
  decide +kernel
end RawCert
