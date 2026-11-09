import Closure371
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1488 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1488 : ∀ h, Pure node1488 h → 11 ≤ h.length := by
  apply indexed_extend node1488 [(0, node452), (5, node760), (8, node715), (10, node813)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower452
  · exact lower760
  · exact lower715
  · exact lower813
def node1489 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1489 : ∀ h, Pure node1489 h → 11 ≤ h.length := by
  apply indexed_extend node1489 [(0, node454), (3, node738), (5, node784), (9, node715), (11, node709)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower454
  · exact lower738
  · exact lower784
  · exact lower715
  · exact lower709
def node1490 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1490 : ∀ h, Pure node1490 h → 11 ≤ h.length := by
  apply indexed_extend node1490 [(0, node455), (4, node728), (5, node785), (9, node715), (13, node708)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower455
  · exact lower728
  · exact lower785
  · exact lower715
  · exact lower708
def node1491 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower1491 : ∀ h, Pure node1491 h → 11 ≤ h.length := by
  apply indexed_extend node1491 [(0, node458), (2, node370), (3, node739), (9, node716), (10, node815), (11, node710)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower458
  · exact lower370
  · exact lower739
  · exact lower716
  · exact lower815
  · exact lower710
def entries372 : List Graph := [node1488, node1489, node1490, node1491]
theorem entries_count372 : entries372.length = 4 := by decide +kernel
theorem census_node1488 : ((verts node1488).filter (wye node1488)).length = 4 := by decide +kernel
theorem census_node1489 : ((verts node1489).filter (wye node1489)).length = 5 := by decide +kernel
theorem census_node1490 : ((verts node1490).filter (wye node1490)).length = 5 := by decide +kernel
theorem census_node1491 : ((verts node1491).filter (wye node1491)).length = 6 := by decide +kernel
theorem arc_count372 : (entries372.map (fun g => ((verts g).filter (wye g)).length)).sum = 20 := by
  simp only [entries372, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1488, census_node1489, census_node1490, census_node1491]
  decide +kernel
end RawCert
