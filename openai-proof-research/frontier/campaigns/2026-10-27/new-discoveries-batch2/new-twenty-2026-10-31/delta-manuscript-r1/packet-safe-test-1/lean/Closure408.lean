import Closure407
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1632 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 2, 0, 0]]
theorem lower1632 : ∀ h, Pure node1632 h → 11 ≤ h.length := by
  apply indexed_extend node1632 [(3, node885), (8, node849), (10, node848)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower885
  · exact lower849
  · exact lower848
def node1633 : Graph := [[0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 1, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower1633 : ∀ h, Pure node1633 h → 11 ≤ h.length := by
  apply indexed_extend node1633 [(5, node861), (7, node868), (10, node852)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower861
  · exact lower868
  · exact lower852
def node1634 : Graph := [[0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1634 : ∀ h, Pure node1634 h → 11 ≤ h.length := by
  apply indexed_extend node1634 [(5, node862), (6, node865), (7, node869), (10, node854), (11, node853)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower862
  · exact lower865
  · exact lower869
  · exact lower854
  · exact lower853
def node1635 : Graph := [[0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower1635 : ∀ h, Pure node1635 h → 11 ≤ h.length := by
  apply indexed_extend node1635 [(5, node863), (6, node866), (7, node870), (11, node853)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower863
  · exact lower866
  · exact lower870
  · exact lower853
def entries408 : List Graph := [node1632, node1633, node1634, node1635]
theorem entries_count408 : entries408.length = 4 := by decide +kernel
theorem census_node1632 : ((verts node1632).filter (wye node1632)).length = 3 := by decide +kernel
theorem census_node1633 : ((verts node1633).filter (wye node1633)).length = 3 := by decide +kernel
theorem census_node1634 : ((verts node1634).filter (wye node1634)).length = 5 := by decide +kernel
theorem census_node1635 : ((verts node1635).filter (wye node1635)).length = 4 := by decide +kernel
theorem arc_count408 : (entries408.map (fun g => ((verts g).filter (wye g)).length)).sum = 15 := by
  simp only [entries408, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1632, census_node1633, census_node1634, census_node1635]
  decide +kernel
end RawCert
