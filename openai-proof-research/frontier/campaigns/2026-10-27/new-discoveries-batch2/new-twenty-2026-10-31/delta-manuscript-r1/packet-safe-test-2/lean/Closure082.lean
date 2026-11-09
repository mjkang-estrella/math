import Closure081
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node328 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower328 : ∀ h, Pure node328 h → 11 ≤ h.length := by
  apply indexed_extend node328 [(4, node146)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower146
def node329 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1], [2, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 0], [0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower329 : ∀ h, Pure node329 h → 11 ≤ h.length := by
  apply indexed_extend node329 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node330 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower330 : ∀ h, Pure node330 h → 11 ≤ h.length := by
  apply indexed_extend node330 [(4, node147), (7, node47)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower147
  · exact lower47
def node331 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower331 : ∀ h, Pure node331 h → 11 ≤ h.length := by
  apply indexed_extend node331 [(6, node45), (7, node48)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower45
  · exact lower48
def entries82 : List Graph := [node328, node329, node330, node331]
theorem entries_count82 : entries82.length = 4 := by decide +kernel
theorem census_node328 : ((verts node328).filter (wye node328)).length = 1 := by decide +kernel
theorem census_node329 : ((verts node329).filter (wye node329)).length = 0 := by decide +kernel
theorem census_node330 : ((verts node330).filter (wye node330)).length = 2 := by decide +kernel
theorem census_node331 : ((verts node331).filter (wye node331)).length = 2 := by decide +kernel
theorem arc_count82 : (entries82.map (fun g => ((verts g).filter (wye g)).length)).sum = 5 := by
  simp only [entries82, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node328, census_node329, census_node330, census_node331]
  decide +kernel
end RawCert
