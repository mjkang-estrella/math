import Closure073
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node296 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 1, 2, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower296 : ∀ h, Pure node296 h → 11 ≤ h.length := by
  apply indexed_extend node296 [(2, node39), (7, node34), (10, node32)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower39
  · exact lower34
  · exact lower32
def node297 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower297 : ∀ h, Pure node297 h → 11 ≤ h.length := by
  apply indexed_extend node297 [(7, node34)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower34
def node298 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 3, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower298 : ∀ h, Pure node298 h → 11 ≤ h.length := by
  apply indexed_extend node298 [(3, node38), (12, node29)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower38
  · exact lower29
def node299 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0], [0, 2, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 3, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower299 : ∀ h, Pure node299 h → 11 ≤ h.length := by
  apply indexed_extend node299 [(4, node39), (12, node30)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower39
  · exact lower30
def entries74 : List Graph := [node296, node297, node298, node299]
theorem entries_count74 : entries74.length = 4 := by decide +kernel
theorem census_node296 : ((verts node296).filter (wye node296)).length = 3 := by decide +kernel
theorem census_node297 : ((verts node297).filter (wye node297)).length = 1 := by decide +kernel
theorem census_node298 : ((verts node298).filter (wye node298)).length = 2 := by decide +kernel
theorem census_node299 : ((verts node299).filter (wye node299)).length = 2 := by decide +kernel
theorem arc_count74 : (entries74.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by
  simp only [entries74, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node296, census_node297, census_node298, census_node299]
  decide +kernel
end RawCert
