import Closure012
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node52 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0]]
theorem lower52 : ∀ h, Pure node52 h → 11 ≤ h.length := by
  apply indexed_extend node52 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node53 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 1], [0, 2, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0]]
theorem lower53 : ∀ h, Pure node53 h → 11 ≤ h.length := by
  apply indexed_extend node53 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node54 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [0, 1, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower54 : ∀ h, Pure node54 h → 11 ≤ h.length := by
  apply indexed_extend node54 [(2, node7), (9, node2)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower7
  · exact lower2
def node55 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 1], [0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0]]
theorem lower55 : ∀ h, Pure node55 h → 11 ≤ h.length := by
  apply indexed_extend node55 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries13 : List Graph := [node52, node53, node54, node55]
theorem entries_count13 : entries13.length = 4 := by decide +kernel
theorem census_node52 : ((verts node52).filter (wye node52)).length = 0 := by decide +kernel
theorem census_node53 : ((verts node53).filter (wye node53)).length = 0 := by decide +kernel
theorem census_node54 : ((verts node54).filter (wye node54)).length = 2 := by decide +kernel
theorem census_node55 : ((verts node55).filter (wye node55)).length = 0 := by decide +kernel
theorem arc_count13 : (entries13.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by
  simp only [entries13, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node52, census_node53, census_node54, census_node55]
  decide +kernel
end RawCert
