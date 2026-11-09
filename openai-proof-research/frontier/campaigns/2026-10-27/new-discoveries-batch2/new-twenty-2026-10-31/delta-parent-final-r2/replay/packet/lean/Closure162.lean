import Closure161
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node648 : Graph := [[0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower648 : ∀ h, Pure node648 h → 11 ≤ h.length := by
  apply indexed_extend node648 [(5, node168), (6, node143)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower168
  · exact lower143
def node649 : Graph := [[0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1], [0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0]]
theorem lower649 : ∀ h, Pure node649 h → 11 ≤ h.length := by
  apply indexed_extend node649 [(5, node171), (6, node144)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower171
  · exact lower144
def node650 : Graph := [[0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower650 : ∀ h, Pure node650 h → 11 ≤ h.length := by
  apply indexed_extend node650 [(5, node175), (8, node144), (12, node143)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower175
  · exact lower144
  · exact lower143
def node651 : Graph := [[0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1], [0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower651 : ∀ h, Pure node651 h → 11 ≤ h.length := by
  apply indexed_extend node651 [(5, node172), (7, node145)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower172
  · exact lower145
def entries162 : List Graph := [node648, node649, node650, node651]
theorem entries_count162 : entries162.length = 4 := by decide +kernel
theorem census_node648 : ((verts node648).filter (wye node648)).length = 2 := by decide +kernel
theorem census_node649 : ((verts node649).filter (wye node649)).length = 2 := by decide +kernel
theorem census_node650 : ((verts node650).filter (wye node650)).length = 3 := by decide +kernel
theorem census_node651 : ((verts node651).filter (wye node651)).length = 2 := by decide +kernel
theorem arc_count162 : (entries162.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries162, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node648, census_node649, census_node650, census_node651]
  decide +kernel
end RawCert
