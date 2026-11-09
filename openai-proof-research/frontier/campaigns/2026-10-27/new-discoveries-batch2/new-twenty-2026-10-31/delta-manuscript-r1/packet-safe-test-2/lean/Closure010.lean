import Closure009
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node40 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1], [0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower40 : ∀ h, Pure node40 h → 11 ≤ h.length := by
  apply indexed_extend node40 [(4, node3)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower3
def node41 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [2, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1], [0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower41 : ∀ h, Pure node41 h → 11 ≤ h.length := by
  apply indexed_extend node41 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node42 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 1], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1, 1, 2, 0, 0]]
theorem lower42 : ∀ h, Pure node42 h → 11 ≤ h.length := by
  apply indexed_extend node42 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node43 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0], [0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3], [0, 1, 1, 2, 0, 0, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0]]
theorem lower43 : ∀ h, Pure node43 h → 11 ≤ h.length := by
  apply indexed_extend node43 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries10 : List Graph := [node40, node41, node42, node43]
theorem entries_count10 : entries10.length = 4 := by decide +kernel
theorem census_node40 : ((verts node40).filter (wye node40)).length = 1 := by decide +kernel
theorem census_node41 : ((verts node41).filter (wye node41)).length = 0 := by decide +kernel
theorem census_node42 : ((verts node42).filter (wye node42)).length = 0 := by decide +kernel
theorem census_node43 : ((verts node43).filter (wye node43)).length = 0 := by decide +kernel
theorem arc_count10 : (entries10.map (fun g => ((verts g).filter (wye g)).length)).sum = 1 := by
  simp only [entries10, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node40, census_node41, census_node42, census_node43]
  decide +kernel
end RawCert
