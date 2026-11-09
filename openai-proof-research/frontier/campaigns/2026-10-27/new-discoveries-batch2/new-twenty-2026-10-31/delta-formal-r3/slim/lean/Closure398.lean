import Closure397
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1592 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1592 : ∀ h, Pure node1592 h → 11 ≤ h.length := by
  apply indexed_extend node1592 [(5, node857), (6, node813), (7, node817), (10, node798)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower857
  · exact lower813
  · exact lower817
  · exact lower798
def node1593 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0]]
theorem lower1593 : ∀ h, Pure node1593 h → 11 ≤ h.length := by
  apply indexed_extend node1593 [(4, node828), (7, node818), (10, node798), (13, node796)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower828
  · exact lower818
  · exact lower798
  · exact lower796
def node1594 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower1594 : ∀ h, Pure node1594 h → 11 ≤ h.length := by
  apply indexed_extend node1594 [(3, node839), (5, node861), (7, node819), (10, node799)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower839
  · exact lower861
  · exact lower819
  · exact lower799
def node1595 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1595 : ∀ h, Pure node1595 h → 11 ≤ h.length := by
  apply indexed_extend node1595 [(3, node840), (5, node862), (7, node820), (10, node801), (11, node800)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower840
  · exact lower862
  · exact lower820
  · exact lower801
  · exact lower800
def entries398 : List Graph := [node1592, node1593, node1594, node1595]
theorem entries_count398 : entries398.length = 4 := by decide +kernel
theorem census_node1592 : ((verts node1592).filter (wye node1592)).length = 4 := by decide +kernel
theorem census_node1593 : ((verts node1593).filter (wye node1593)).length = 4 := by decide +kernel
theorem census_node1594 : ((verts node1594).filter (wye node1594)).length = 4 := by decide +kernel
theorem census_node1595 : ((verts node1595).filter (wye node1595)).length = 5 := by decide +kernel
theorem arc_count398 : (entries398.map (fun g => ((verts g).filter (wye g)).length)).sum = 17 := by
  simp only [entries398, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1592, census_node1593, census_node1594, census_node1595]
  decide +kernel
end RawCert
