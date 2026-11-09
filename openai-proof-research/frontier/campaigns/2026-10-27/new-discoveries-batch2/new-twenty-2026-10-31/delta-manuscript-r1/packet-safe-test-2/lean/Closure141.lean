import Closure140
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node564 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0], [0, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0]]
theorem lower564 : ∀ h, Pure node564 h → 11 ≤ h.length := by
  apply indexed_extend node564 [(5, node120), (6, node128)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower120
  · exact lower128
def node565 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 1], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 2, 0]]
theorem lower565 : ∀ h, Pure node565 h → 11 ≤ h.length := by
  apply indexed_extend node565 [(5, node121), (8, node118)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower121
  · exact lower118
def node566 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 2, 0]]
theorem lower566 : ∀ h, Pure node566 h → 11 ≤ h.length := by
  apply indexed_extend node566 [(5, node122)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower122
def node567 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0]]
theorem lower567 : ∀ h, Pure node567 h → 11 ≤ h.length := by
  apply indexed_extend node567 [(4, node123)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower123
def entries141 : List Graph := [node564, node565, node566, node567]
theorem entries_count141 : entries141.length = 4 := by decide +kernel
theorem census_node564 : ((verts node564).filter (wye node564)).length = 2 := by decide +kernel
theorem census_node565 : ((verts node565).filter (wye node565)).length = 2 := by decide +kernel
theorem census_node566 : ((verts node566).filter (wye node566)).length = 1 := by decide +kernel
theorem census_node567 : ((verts node567).filter (wye node567)).length = 1 := by decide +kernel
theorem arc_count141 : (entries141.map (fun g => ((verts g).filter (wye g)).length)).sum = 6 := by
  simp only [entries141, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node564, census_node565, census_node566, census_node567]
  decide +kernel
end RawCert
