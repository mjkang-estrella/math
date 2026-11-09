import Closure350
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1404 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0]]
theorem lower1404 : ∀ h, Pure node1404 h → 11 ≤ h.length := by
  apply indexed_extend node1404 [(5, node633), (6, node634), (10, node618), (12, node614), (13, node613)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower633
  · exact lower634
  · exact lower618
  · exact lower614
  · exact lower613
def node1405 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0]]
theorem lower1405 : ∀ h, Pure node1405 h → 11 ≤ h.length := by
  apply indexed_extend node1405 [(5, node633), (7, node635), (10, node619), (12, node616), (13, node615)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower633
  · exact lower635
  · exact lower619
  · exact lower616
  · exact lower615
def node1406 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 2, 0]]
theorem lower1406 : ∀ h, Pure node1406 h → 11 ≤ h.length := by
  apply indexed_extend node1406 [(5, node634), (7, node636), (10, node620), (12, node617)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower634
  · exact lower636
  · exact lower620
  · exact lower617
def node1407 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0]]
theorem lower1407 : ∀ h, Pure node1407 h → 11 ≤ h.length := by
  apply indexed_extend node1407 [(6, node635), (7, node636), (12, node622), (13, node621)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower635
  · exact lower636
  · exact lower622
  · exact lower621
def entries351 : List Graph := [node1404, node1405, node1406, node1407]
theorem entries_count351 : entries351.length = 4 := by decide +kernel
theorem census_node1404 : ((verts node1404).filter (wye node1404)).length = 5 := by decide +kernel
theorem census_node1405 : ((verts node1405).filter (wye node1405)).length = 5 := by decide +kernel
theorem census_node1406 : ((verts node1406).filter (wye node1406)).length = 4 := by decide +kernel
theorem census_node1407 : ((verts node1407).filter (wye node1407)).length = 4 := by decide +kernel
theorem arc_count351 : (entries351.map (fun g => ((verts g).filter (wye g)).length)).sum = 18 := by
  simp only [entries351, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1404, census_node1405, census_node1406, census_node1407]
  decide +kernel
end RawCert
