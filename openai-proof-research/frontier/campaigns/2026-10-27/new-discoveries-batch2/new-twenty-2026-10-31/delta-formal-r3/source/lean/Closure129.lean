import Closure128
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node516 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower516 : ∀ h, Pure node516 h → 11 ≤ h.length := by
  apply indexed_extend node516 [(5, node107), (8, node106), (12, node97)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower107
  · exact lower106
  · exact lower97
def node517 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower517 : ∀ h, Pure node517 h → 11 ≤ h.length := by
  apply indexed_extend node517 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node518 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0], [1, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower518 : ∀ h, Pure node518 h → 11 ≤ h.length := by
  apply indexed_extend node518 [(5, node108)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower108
def node519 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower519 : ∀ h, Pure node519 h → 11 ≤ h.length := by
  apply indexed_extend node519 [(7, node108)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower108
def entries129 : List Graph := [node516, node517, node518, node519]
theorem entries_count129 : entries129.length = 4 := by decide +kernel
theorem census_node516 : ((verts node516).filter (wye node516)).length = 3 := by decide +kernel
theorem census_node517 : ((verts node517).filter (wye node517)).length = 0 := by decide +kernel
theorem census_node518 : ((verts node518).filter (wye node518)).length = 1 := by decide +kernel
theorem census_node519 : ((verts node519).filter (wye node519)).length = 1 := by decide +kernel
theorem arc_count129 : (entries129.map (fun g => ((verts g).filter (wye g)).length)).sum = 5 := by
  simp only [entries129, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node516, census_node517, census_node518, census_node519]
  decide +kernel
end RawCert
