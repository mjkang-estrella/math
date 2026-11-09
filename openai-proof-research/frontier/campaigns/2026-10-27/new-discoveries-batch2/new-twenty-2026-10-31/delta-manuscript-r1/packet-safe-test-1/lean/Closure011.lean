import Closure010
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node44 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0], [0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 1], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3], [0, 1, 1, 2, 0, 0, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0]]
theorem lower44 : ∀ h, Pure node44 h → 11 ≤ h.length := by
  apply indexed_extend node44 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node45 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]]
theorem lower45 : ∀ h, Pure node45 h → 11 ≤ h.length := by
  apply indexed_extend node45 [(6, node2)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower2
def node46 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0], [0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0]]
theorem lower46 : ∀ h, Pure node46 h → 11 ≤ h.length := by
  apply indexed_extend node46 [(4, node9), (7, node2)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower9
  · exact lower2
def node47 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 2], [0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0], [0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 0, 2, 0, 1, 0, 1, 0]]
theorem lower47 : ∀ h, Pure node47 h → 11 ≤ h.length := by
  apply indexed_extend node47 [(4, node10)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower10
def entries11 : List Graph := [node44, node45, node46, node47]
theorem entries_count11 : entries11.length = 4 := by decide +kernel
theorem census_node44 : ((verts node44).filter (wye node44)).length = 0 := by decide +kernel
theorem census_node45 : ((verts node45).filter (wye node45)).length = 1 := by decide +kernel
theorem census_node46 : ((verts node46).filter (wye node46)).length = 2 := by decide +kernel
theorem census_node47 : ((verts node47).filter (wye node47)).length = 1 := by decide +kernel
theorem arc_count11 : (entries11.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by
  simp only [entries11, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node44, census_node45, census_node46, census_node47]
  decide +kernel
end RawCert
