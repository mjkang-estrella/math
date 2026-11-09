import Closure046
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node188 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower188 : ∀ h, Pure node188 h → 11 ≤ h.length := by
  apply indexed_extend node188 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node189 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1], [1, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower189 : ∀ h, Pure node189 h → 11 ≤ h.length := by
  apply indexed_extend node189 [(2, node11), (4, node15)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower11
  · exact lower15
def node190 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [2, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [0, 0, 1, 0, 0, 0, 2, 1, 1, 0, 1, 0], [0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 1, 1, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower190 : ∀ h, Pure node190 h → 11 ≤ h.length := by
  apply indexed_extend node190 [(6, node15), (9, node19)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower15
  · exact lower19
def node191 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0], [1, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower191 : ∀ h, Pure node191 h → 11 ≤ h.length := by
  apply indexed_extend node191 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries47 : List Graph := [node188, node189, node190, node191]
theorem entries_count47 : entries47.length = 4 := by decide +kernel
theorem census_node188 : ((verts node188).filter (wye node188)).length = 0 := by decide +kernel
theorem census_node189 : ((verts node189).filter (wye node189)).length = 2 := by decide +kernel
theorem census_node190 : ((verts node190).filter (wye node190)).length = 2 := by decide +kernel
theorem census_node191 : ((verts node191).filter (wye node191)).length = 0 := by decide +kernel
theorem arc_count47 : (entries47.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by
  simp only [entries47, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node188, census_node189, census_node190, census_node191]
  decide +kernel
end RawCert
