import Closure209
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node840 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower840 : ∀ h, Pure node840 h → 11 ≤ h.length := by
  apply indexed_extend node840 [(6, node225)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower225
def node841 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower841 : ∀ h, Pure node841 h → 11 ≤ h.length := by
  apply indexed_extend node841 [(6, node226), (8, node220)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower226
  · exact lower220
def node842 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0, 0]]
theorem lower842 : ∀ h, Pure node842 h → 11 ≤ h.length := by
  apply indexed_extend node842 [(6, node227), (9, node220)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower227
  · exact lower220
def node843 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 3], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower843 : ∀ h, Pure node843 h → 11 ≤ h.length := by
  apply indexed_extend node843 [(5, node224), (8, node221)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower224
  · exact lower221
def entries210 : List Graph := [node840, node841, node842, node843]
theorem entries_count210 : entries210.length = 4 := by decide +kernel
theorem census_node840 : ((verts node840).filter (wye node840)).length = 1 := by decide +kernel
theorem census_node841 : ((verts node841).filter (wye node841)).length = 2 := by decide +kernel
theorem census_node842 : ((verts node842).filter (wye node842)).length = 2 := by decide +kernel
theorem census_node843 : ((verts node843).filter (wye node843)).length = 2 := by decide +kernel
theorem arc_count210 : (entries210.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by
  simp only [entries210, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node840, census_node841, census_node842, census_node843]
  decide +kernel
end RawCert
