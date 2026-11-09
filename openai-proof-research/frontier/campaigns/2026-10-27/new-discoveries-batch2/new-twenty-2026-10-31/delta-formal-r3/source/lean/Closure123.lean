import Closure122
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node492 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower492 : ∀ h, Pure node492 h → 11 ≤ h.length := by
  apply indexed_extend node492 [(6, node96)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower96
def node493 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1], [2, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0], [1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower493 : ∀ h, Pure node493 h → 11 ≤ h.length := by
  apply indexed_extend node493 [(6, node97)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower97
def node494 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower494 : ∀ h, Pure node494 h → 11 ≤ h.length := by
  apply indexed_extend node494 [(6, node96), (7, node97)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower96
  · exact lower97
def node495 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower495 : ∀ h, Pure node495 h → 11 ≤ h.length := by
  apply indexed_extend node495 [(2, node186)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower186
def entries123 : List Graph := [node492, node493, node494, node495]
theorem entries_count123 : entries123.length = 4 := by decide +kernel
theorem census_node492 : ((verts node492).filter (wye node492)).length = 1 := by decide +kernel
theorem census_node493 : ((verts node493).filter (wye node493)).length = 1 := by decide +kernel
theorem census_node494 : ((verts node494).filter (wye node494)).length = 2 := by decide +kernel
theorem census_node495 : ((verts node495).filter (wye node495)).length = 1 := by decide +kernel
theorem arc_count123 : (entries123.map (fun g => ((verts g).filter (wye g)).length)).sum = 5 := by
  simp only [entries123, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node492, census_node493, census_node494, census_node495]
  decide +kernel
end RawCert
