import Closure025
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node104 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [2, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 1, 0, 0, 0, 2, 1, 0]]
theorem lower104 : ∀ h, Pure node104 h → 11 ≤ h.length := by
  apply indexed_extend node104 [(6, node7)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower7
def node105 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [2, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 2], [0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower105 : ∀ h, Pure node105 h → 11 ≤ h.length := by
  apply indexed_extend node105 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node106 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [2, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0], [1, 0, 0, 1, 0, 2, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower106 : ∀ h, Pure node106 h → 11 ≤ h.length := by
  apply indexed_extend node106 [(5, node7)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower7
def node107 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 1], [0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 1, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0, 0]]
theorem lower107 : ∀ h, Pure node107 h → 11 ≤ h.length := by
  apply indexed_extend node107 [(7, node7)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower7
def entries26 : List Graph := [node104, node105, node106, node107]
theorem entries_count26 : entries26.length = 4 := by decide +kernel
theorem census_node104 : ((verts node104).filter (wye node104)).length = 1 := by decide +kernel
theorem census_node105 : ((verts node105).filter (wye node105)).length = 0 := by decide +kernel
theorem census_node106 : ((verts node106).filter (wye node106)).length = 1 := by decide +kernel
theorem census_node107 : ((verts node107).filter (wye node107)).length = 1 := by decide +kernel
theorem arc_count26 : (entries26.map (fun g => ((verts g).filter (wye g)).length)).sum = 3 := by
  simp only [entries26, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node104, census_node105, census_node106, census_node107]
  decide +kernel
end RawCert
