import Closure145
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node584 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2, 0, 0]]
theorem lower584 : ∀ h, Pure node584 h → 11 ≤ h.length := by
  apply indexed_extend node584 [(1, node218), (11, node121)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower218
  · exact lower121
def node585 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [2, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [1, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 2], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 2, 0, 0]]
theorem lower585 : ∀ h, Pure node585 h → 11 ≤ h.length := by
  apply indexed_extend node585 [(1, node219), (11, node122)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower219
  · exact lower122
def node586 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0]]
theorem lower586 : ∀ h, Pure node586 h → 11 ≤ h.length := by
  apply indexed_extend node586 [(1, node223), (2, node220), (7, node124)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower223
  · exact lower220
  · exact lower124
def node587 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0], [0, 0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 1, 0], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower587 : ∀ h, Pure node587 h → 11 ≤ h.length := by
  apply indexed_extend node587 [(2, node221), (12, node123)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower221
  · exact lower123
def entries146 : List Graph := [node584, node585, node586, node587]
theorem entries_count146 : entries146.length = 4 := by decide +kernel
theorem census_node584 : ((verts node584).filter (wye node584)).length = 2 := by decide +kernel
theorem census_node585 : ((verts node585).filter (wye node585)).length = 2 := by decide +kernel
theorem census_node586 : ((verts node586).filter (wye node586)).length = 3 := by decide +kernel
theorem census_node587 : ((verts node587).filter (wye node587)).length = 2 := by decide +kernel
theorem arc_count146 : (entries146.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries146, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node584, census_node585, census_node586, census_node587]
  decide +kernel
end RawCert
