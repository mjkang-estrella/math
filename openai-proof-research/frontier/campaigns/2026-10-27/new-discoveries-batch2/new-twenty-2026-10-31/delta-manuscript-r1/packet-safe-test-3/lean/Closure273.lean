import Closure272
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1092 : Graph := [[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1092 : ∀ h, Pure node1092 h → 11 ≤ h.length := by
  apply indexed_extend node1092 [(5, node391), (9, node383), (13, node379)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower391
  · exact lower383
  · exact lower379
def node1093 : Graph := [[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 1, 2, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1093 : ∀ h, Pure node1093 h → 11 ≤ h.length := by
  apply indexed_extend node1093 [(6, node396), (9, node384), (13, node380)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower396
  · exact lower384
  · exact lower380
def node1094 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1094 : ∀ h, Pure node1094 h → 11 ≤ h.length := by
  apply indexed_extend node1094 [(2, node648), (6, node430), (7, node386), (9, node385)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower648
  · exact lower430
  · exact lower386
  · exact lower385
def node1095 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0]]
theorem lower1095 : ∀ h, Pure node1095 h → 11 ≤ h.length := by
  apply indexed_extend node1095 [(6, node433), (7, node389), (10, node387)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower433
  · exact lower389
  · exact lower387
def entries273 : List Graph := [node1092, node1093, node1094, node1095]
theorem entries_count273 : entries273.length = 4 := by decide +kernel
theorem census_node1092 : ((verts node1092).filter (wye node1092)).length = 3 := by decide +kernel
theorem census_node1093 : ((verts node1093).filter (wye node1093)).length = 3 := by decide +kernel
theorem census_node1094 : ((verts node1094).filter (wye node1094)).length = 4 := by decide +kernel
theorem census_node1095 : ((verts node1095).filter (wye node1095)).length = 3 := by decide +kernel
theorem arc_count273 : (entries273.map (fun g => ((verts g).filter (wye g)).length)).sum = 13 := by
  simp only [entries273, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1092, census_node1093, census_node1094, census_node1095]
  decide +kernel
end RawCert
