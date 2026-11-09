import Closure107
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node432 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0], [0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower432 : ∀ h, Pure node432 h → 11 ≤ h.length := by
  apply indexed_extend node432 [(2, node170)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower170
def node433 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0], [1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower433 : ∀ h, Pure node433 h → 11 ≤ h.length := by
  apply indexed_extend node433 [(6, node80), (9, node75)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower80
  · exact lower75
def node434 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0], [0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower434 : ∀ h, Pure node434 h → 11 ≤ h.length := by
  apply indexed_extend node434 [(2, node171), (6, node81), (10, node75)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower171
  · exact lower81
  · exact lower75
def node435 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0], [1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0]]
theorem lower435 : ∀ h, Pure node435 h → 11 ≤ h.length := by
  apply indexed_extend node435 [(7, node82), (9, node76)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower82
  · exact lower76
def entries108 : List Graph := [node432, node433, node434, node435]
theorem entries_count108 : entries108.length = 4 := by decide +kernel
theorem census_node432 : ((verts node432).filter (wye node432)).length = 1 := by decide +kernel
theorem census_node433 : ((verts node433).filter (wye node433)).length = 2 := by decide +kernel
theorem census_node434 : ((verts node434).filter (wye node434)).length = 3 := by decide +kernel
theorem census_node435 : ((verts node435).filter (wye node435)).length = 2 := by decide +kernel
theorem arc_count108 : (entries108.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by
  simp only [entries108, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node432, census_node433, census_node434, census_node435]
  decide +kernel
end RawCert
