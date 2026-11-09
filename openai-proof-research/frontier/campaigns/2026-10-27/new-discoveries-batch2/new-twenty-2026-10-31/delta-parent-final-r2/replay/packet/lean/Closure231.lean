import Closure230
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node924 : Graph := [[0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0, 0]]
theorem lower924 : ∀ h, Pure node924 h → 11 ≤ h.length := by
  apply indexed_extend node924 [(1, node176), (8, node259), (11, node282)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower176
  · exact lower259
  · exact lower282
def node925 : Graph := [[0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1], [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0], [1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower925 : ∀ h, Pure node925 h → 11 ≤ h.length := by
  apply indexed_extend node925 [(4, node260), (6, node262)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower260
  · exact lower262
def node926 : Graph := [[0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 1, 0, 0, 1, 0, 1, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1], [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0], [1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower926 : ∀ h, Pure node926 h → 11 ≤ h.length := by
  apply indexed_extend node926 [(4, node261)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower261
def node927 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower927 : ∀ h, Pure node927 h → 11 ≤ h.length := by
  apply indexed_extend node927 [(3, node267), (5, node264), (9, node260)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower267
  · exact lower264
  · exact lower260
def entries231 : List Graph := [node924, node925, node926, node927]
theorem entries_count231 : entries231.length = 4 := by decide +kernel
theorem census_node924 : ((verts node924).filter (wye node924)).length = 3 := by decide +kernel
theorem census_node925 : ((verts node925).filter (wye node925)).length = 2 := by decide +kernel
theorem census_node926 : ((verts node926).filter (wye node926)).length = 1 := by decide +kernel
theorem census_node927 : ((verts node927).filter (wye node927)).length = 3 := by decide +kernel
theorem arc_count231 : (entries231.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries231, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node924, census_node925, census_node926, census_node927]
  decide +kernel
end RawCert
