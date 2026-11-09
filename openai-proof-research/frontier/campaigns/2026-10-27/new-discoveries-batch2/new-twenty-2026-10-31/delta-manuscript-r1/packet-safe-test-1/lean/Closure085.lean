import Closure084
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node340 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower340 : ∀ h, Pure node340 h → 11 ≤ h.length := by
  apply indexed_extend node340 [(3, node93), (4, node150)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower93
  · exact lower150
def node341 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [2, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 0], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower341 : ∀ h, Pure node341 h → 11 ≤ h.length := by
  apply indexed_extend node341 [(3, node94)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower94
def node342 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower342 : ∀ h, Pure node342 h → 11 ≤ h.length := by
  apply indexed_extend node342 [(4, node151)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower151
def node343 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower343 : ∀ h, Pure node343 h → 11 ≤ h.length := by
  apply indexed_extend node343 [(6, node50)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower50
def entries85 : List Graph := [node340, node341, node342, node343]
theorem entries_count85 : entries85.length = 4 := by decide +kernel
theorem census_node340 : ((verts node340).filter (wye node340)).length = 2 := by decide +kernel
theorem census_node341 : ((verts node341).filter (wye node341)).length = 1 := by decide +kernel
theorem census_node342 : ((verts node342).filter (wye node342)).length = 1 := by decide +kernel
theorem census_node343 : ((verts node343).filter (wye node343)).length = 1 := by decide +kernel
theorem arc_count85 : (entries85.map (fun g => ((verts g).filter (wye g)).length)).sum = 5 := by
  simp only [entries85, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node340, census_node341, census_node342, census_node343]
  decide +kernel
end RawCert
