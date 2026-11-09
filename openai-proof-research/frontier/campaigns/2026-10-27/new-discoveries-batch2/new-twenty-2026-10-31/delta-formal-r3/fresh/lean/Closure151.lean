import Closure150
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node604 : Graph := [[0, 0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0]]
theorem lower604 : ∀ h, Pure node604 h → 11 ≤ h.length := by
  apply indexed_extend node604 [(8, node126)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower126
def node605 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0]]
theorem lower605 : ∀ h, Pure node605 h → 11 ≤ h.length := by
  apply indexed_extend node605 [(5, node127), (6, node128)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower127
  · exact lower128
def node606 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1, 0], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower606 : ∀ h, Pure node606 h → 11 ≤ h.length := by
  apply indexed_extend node606 [(1, node228), (5, node129), (12, node127)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower228
  · exact lower129
  · exact lower127
def node607 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower607 : ∀ h, Pure node607 h → 11 ≤ h.length := by
  apply indexed_extend node607 [(1, node235), (2, node229), (5, node129), (12, node128)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower235
  · exact lower229
  · exact lower129
  · exact lower128
def entries151 : List Graph := [node604, node605, node606, node607]
theorem entries_count151 : entries151.length = 4 := by decide +kernel
theorem census_node604 : ((verts node604).filter (wye node604)).length = 1 := by decide +kernel
theorem census_node605 : ((verts node605).filter (wye node605)).length = 2 := by decide +kernel
theorem census_node606 : ((verts node606).filter (wye node606)).length = 3 := by decide +kernel
theorem census_node607 : ((verts node607).filter (wye node607)).length = 4 := by decide +kernel
theorem arc_count151 : (entries151.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries151, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node604, census_node605, census_node606, census_node607]
  decide +kernel
end RawCert
