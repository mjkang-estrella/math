import Closure148
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node596 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0]]
theorem lower596 : ∀ h, Pure node596 h → 11 ≤ h.length := by
  apply indexed_extend node596 [(4, node142), (7, node126)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower142
  · exact lower126
def node597 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0]]
theorem lower597 : ∀ h, Pure node597 h → 11 ≤ h.length := by
  apply indexed_extend node597 [(6, node125), (9, node123)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower125
  · exact lower123
def node598 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0], [0, 0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0]]
theorem lower598 : ∀ h, Pure node598 h → 11 ≤ h.length := by
  apply indexed_extend node598 [(7, node126), (12, node123)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower126
  · exact lower123
def node599 : Graph := [[0, 0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower599 : ∀ h, Pure node599 h → 11 ≤ h.length := by
  apply indexed_extend node599 [(2, node224), (12, node125)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower224
  · exact lower125
def entries149 : List Graph := [node596, node597, node598, node599]
theorem entries_count149 : entries149.length = 4 := by decide +kernel
theorem census_node596 : ((verts node596).filter (wye node596)).length = 2 := by decide +kernel
theorem census_node597 : ((verts node597).filter (wye node597)).length = 2 := by decide +kernel
theorem census_node598 : ((verts node598).filter (wye node598)).length = 2 := by decide +kernel
theorem census_node599 : ((verts node599).filter (wye node599)).length = 2 := by decide +kernel
theorem arc_count149 : (entries149.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by
  simp only [entries149, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node596, census_node597, census_node598, census_node599]
  decide +kernel
end RawCert
