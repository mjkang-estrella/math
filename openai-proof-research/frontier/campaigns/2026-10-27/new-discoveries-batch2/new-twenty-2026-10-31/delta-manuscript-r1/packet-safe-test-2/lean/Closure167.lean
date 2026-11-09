import Closure166
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node668 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower668 : ∀ h, Pure node668 h → 11 ≤ h.length := by
  apply indexed_extend node668 [(8, node153), (12, node146)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower153
  · exact lower146
def node669 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower669 : ∀ h, Pure node669 h → 11 ≤ h.length := by
  apply indexed_extend node669 [(5, node160), (8, node154), (10, node148)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower160
  · exact lower154
  · exact lower148
def node670 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower670 : ∀ h, Pure node670 h → 11 ≤ h.length := by
  apply indexed_extend node670 [(8, node154)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower154
def node671 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower671 : ∀ h, Pure node671 h → 11 ≤ h.length := by
  apply indexed_extend node671 [(5, node160), (6, node161), (10, node149)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower160
  · exact lower161
  · exact lower149
def entries167 : List Graph := [node668, node669, node670, node671]
theorem entries_count167 : entries167.length = 4 := by decide +kernel
theorem census_node668 : ((verts node668).filter (wye node668)).length = 2 := by decide +kernel
theorem census_node669 : ((verts node669).filter (wye node669)).length = 3 := by decide +kernel
theorem census_node670 : ((verts node670).filter (wye node670)).length = 1 := by decide +kernel
theorem census_node671 : ((verts node671).filter (wye node671)).length = 3 := by decide +kernel
theorem arc_count167 : (entries167.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries167, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node668, census_node669, census_node670, census_node671]
  decide +kernel
end RawCert
