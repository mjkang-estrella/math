import Closure507
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2032 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower2032 : ∀ h, Pure node2032 h → 11 ≤ h.length := by
  apply indexed_extend node2032 [(0, node1088), (2, node1023), (7, node1453), (8, node1461), (11, node1447), (12, node1584)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1088
  · exact lower1023
  · exact lower1453
  · exact lower1461
  · exact lower1447
  · exact lower1584
def node2033 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower2033 : ∀ h, Pure node2033 h → 11 ≤ h.length := by
  apply indexed_extend node2033 [(0, node1094), (3, node1504), (5, node1543), (7, node1455), (8, node1449), (10, node1448), (12, node1594)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1094
  · exact lower1504
  · exact lower1543
  · exact lower1455
  · exact lower1449
  · exact lower1448
  · exact lower1594
def node2034 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0]]
theorem lower2034 : ∀ h, Pure node2034 h → 11 ≤ h.length := by
  apply indexed_extend node2034 [(0, node1095), (5, node1544), (7, node1458), (8, node1451), (11, node1450), (12, node1596)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1095
  · exact lower1544
  · exact lower1458
  · exact lower1451
  · exact lower1450
  · exact lower1596
def node2035 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 2, 0, 0, 0]]
theorem lower2035 : ∀ h, Pure node2035 h → 11 ≤ h.length := by
  apply indexed_extend node2035 [(0, node1099), (2, node1024), (5, node1545), (7, node1459), (9, node1453), (11, node1452), (12, node1599)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1099
  · exact lower1024
  · exact lower1545
  · exact lower1459
  · exact lower1453
  · exact lower1452
  · exact lower1599
def entries508 : List Graph := [node2032, node2033, node2034, node2035]
theorem entries_count508 : entries508.length = 4 := by decide +kernel
theorem census_node2032 : ((verts node2032).filter (wye node2032)).length = 6 := by decide +kernel
theorem census_node2033 : ((verts node2033).filter (wye node2033)).length = 7 := by decide +kernel
theorem census_node2034 : ((verts node2034).filter (wye node2034)).length = 6 := by decide +kernel
theorem census_node2035 : ((verts node2035).filter (wye node2035)).length = 7 := by decide +kernel
theorem arc_count508 : (entries508.map (fun g => ((verts g).filter (wye g)).length)).sum = 26 := by
  simp only [entries508, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node2032, census_node2033, census_node2034, census_node2035]
  decide +kernel
end RawCert
