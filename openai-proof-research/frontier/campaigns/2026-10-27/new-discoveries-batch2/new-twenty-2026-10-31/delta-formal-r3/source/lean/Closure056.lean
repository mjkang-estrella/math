import Closure055
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node224 : Graph := [[0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [1, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower224 : ∀ h, Pure node224 h → 11 ≤ h.length := by
  apply indexed_extend node224 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node225 : Graph := [[0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [1, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower225 : ∀ h, Pure node225 h → 11 ≤ h.length := by
  apply indexed_extend node225 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node226 : Graph := [[0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower226 : ∀ h, Pure node226 h → 11 ≤ h.length := by
  apply indexed_extend node226 [(7, node18)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower18
def node227 : Graph := [[0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [2, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 1], [1, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 2, 2, 0, 0]]
theorem lower227 : ∀ h, Pure node227 h → 11 ≤ h.length := by
  apply indexed_extend node227 [(8, node18)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower18
def entries56 : List Graph := [node224, node225, node226, node227]
theorem entries_count56 : entries56.length = 4 := by decide +kernel
theorem census_node224 : ((verts node224).filter (wye node224)).length = 0 := by decide +kernel
theorem census_node225 : ((verts node225).filter (wye node225)).length = 0 := by decide +kernel
theorem census_node226 : ((verts node226).filter (wye node226)).length = 1 := by decide +kernel
theorem census_node227 : ((verts node227).filter (wye node227)).length = 1 := by decide +kernel
theorem arc_count56 : (entries56.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by
  simp only [entries56, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node224, census_node225, census_node226, census_node227]
  decide +kernel
end RawCert
