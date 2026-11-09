import Closure064
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node260 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1], [2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0], [1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1], [0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower260 : ∀ h, Pure node260 h → 11 ≤ h.length := by
  apply indexed_extend node260 [(5, node22)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower22
def node261 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [0, 0, 1, 2, 0, 1, 0, 0, 1, 0, 1, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1], [2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0], [1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower261 : ∀ h, Pure node261 h → 11 ≤ h.length := by
  apply indexed_extend node261 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node262 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3], [0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1], [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0], [1, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower262 : ∀ h, Pure node262 h → 11 ≤ h.length := by
  apply indexed_extend node262 [(4, node22)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower22
def node263 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 0, 1], [2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0], [1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0]]
theorem lower263 : ∀ h, Pure node263 h → 11 ≤ h.length := by
  apply indexed_extend node263 [(7, node22)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower22
def entries65 : List Graph := [node260, node261, node262, node263]
theorem entries_count65 : entries65.length = 4 := by decide +kernel
theorem census_node260 : ((verts node260).filter (wye node260)).length = 1 := by decide +kernel
theorem census_node261 : ((verts node261).filter (wye node261)).length = 0 := by decide +kernel
theorem census_node262 : ((verts node262).filter (wye node262)).length = 1 := by decide +kernel
theorem census_node263 : ((verts node263).filter (wye node263)).length = 1 := by decide +kernel
theorem arc_count65 : (entries65.map (fun g => ((verts g).filter (wye g)).length)).sum = 3 := by
  simp only [entries65, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node260, census_node261, census_node262, census_node263]
  decide +kernel
end RawCert
