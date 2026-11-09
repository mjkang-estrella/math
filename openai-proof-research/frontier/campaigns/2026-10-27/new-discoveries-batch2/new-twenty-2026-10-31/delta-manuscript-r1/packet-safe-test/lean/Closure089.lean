import Closure088
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node356 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 2, 0]]
theorem lower356 : ∀ h, Pure node356 h → 11 ≤ h.length := by
  apply indexed_extend node356 [(7, node52)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower52
def node357 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower357 : ∀ h, Pure node357 h → 11 ≤ h.length := by
  apply indexed_extend node357 [(12, node43)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower43
def node358 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower358 : ∀ h, Pure node358 h → 11 ≤ h.length := by
  apply indexed_extend node358 [(6, node52), (12, node44)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower52
  · exact lower44
def node359 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 2], [0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower359 : ∀ h, Pure node359 h → 11 ≤ h.length := by
  apply indexed_extend node359 [(4, node153)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower153
def entries89 : List Graph := [node356, node357, node358, node359]
theorem entries_count89 : entries89.length = 4 := by decide +kernel
theorem census_node356 : ((verts node356).filter (wye node356)).length = 1 := by decide +kernel
theorem census_node357 : ((verts node357).filter (wye node357)).length = 1 := by decide +kernel
theorem census_node358 : ((verts node358).filter (wye node358)).length = 2 := by decide +kernel
theorem census_node359 : ((verts node359).filter (wye node359)).length = 1 := by decide +kernel
theorem arc_count89 : (entries89.map (fun g => ((verts g).filter (wye g)).length)).sum = 5 := by
  simp only [entries89, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node356, census_node357, census_node358, census_node359]
  decide +kernel
end RawCert
