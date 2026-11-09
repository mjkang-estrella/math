import Closure427
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1712 : Graph := [[0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 2], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1712 : ∀ h, Pure node1712 h → 11 ≤ h.length := by
  apply indexed_extend node1712 [(1, node687), (5, node923), (9, node921), (12, node969), (13, node917)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower687
  · exact lower923
  · exact lower921
  · exact lower969
  · exact lower917
def node1713 : Graph := [[0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1713 : ∀ h, Pure node1713 h → 11 ≤ h.length := by
  apply indexed_extend node1713 [(1, node688), (6, node924), (9, node922), (12, node970), (13, node918)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower688
  · exact lower924
  · exact lower922
  · exact lower970
  · exact lower918
def node1714 : Graph := [[0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower1714 : ∀ h, Pure node1714 h → 11 ≤ h.length := by
  apply indexed_extend node1714 [(3, node936), (4, node927), (6, node933), (8, node959), (10, node925)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower936
  · exact lower927
  · exact lower933
  · exact lower959
  · exact lower925
def node1715 : Graph := [[0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower1715 : ∀ h, Pure node1715 h → 11 ≤ h.length := by
  apply indexed_extend node1715 [(3, node937), (4, node928), (8, node960), (10, node926)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower937
  · exact lower928
  · exact lower960
  · exact lower926
def entries428 : List Graph := [node1712, node1713, node1714, node1715]
theorem entries_count428 : entries428.length = 4 := by decide +kernel
theorem census_node1712 : ((verts node1712).filter (wye node1712)).length = 5 := by decide +kernel
theorem census_node1713 : ((verts node1713).filter (wye node1713)).length = 5 := by decide +kernel
theorem census_node1714 : ((verts node1714).filter (wye node1714)).length = 5 := by decide +kernel
theorem census_node1715 : ((verts node1715).filter (wye node1715)).length = 4 := by decide +kernel
theorem arc_count428 : (entries428.map (fun g => ((verts g).filter (wye g)).length)).sum = 19 := by
  simp only [entries428, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1712, census_node1713, census_node1714, census_node1715]
  decide +kernel
end RawCert
