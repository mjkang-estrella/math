import Closure034
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node140 : Graph := [[0, 0, 0, 3, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1], [0, 0, 0, 2, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0]]
theorem lower140 : ∀ h, Pure node140 h → 11 ≤ h.length := by
  apply indexed_extend node140 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node141 : Graph := [[0, 0, 0, 3, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0]]
theorem lower141 : ∀ h, Pure node141 h → 11 ≤ h.length := by
  apply indexed_extend node141 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node142 : Graph := [[0, 0, 0, 3, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0], [0, 0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0]]
theorem lower142 : ∀ h, Pure node142 h → 11 ≤ h.length := by
  apply indexed_extend node142 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node143 : Graph := [[0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3], [0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower143 : ∀ h, Pure node143 h → 11 ≤ h.length := by
  apply indexed_extend node143 [(5, node12)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower12
def entries35 : List Graph := [node140, node141, node142, node143]
theorem entries_count35 : entries35.length = 4 := by decide +kernel
theorem census_node140 : ((verts node140).filter (wye node140)).length = 0 := by decide +kernel
theorem census_node141 : ((verts node141).filter (wye node141)).length = 0 := by decide +kernel
theorem census_node142 : ((verts node142).filter (wye node142)).length = 0 := by decide +kernel
theorem census_node143 : ((verts node143).filter (wye node143)).length = 1 := by decide +kernel
theorem arc_count35 : (entries35.map (fun g => ((verts g).filter (wye g)).length)).sum = 1 := by
  simp only [entries35, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node140, census_node141, census_node142, census_node143]
  decide +kernel
end RawCert
