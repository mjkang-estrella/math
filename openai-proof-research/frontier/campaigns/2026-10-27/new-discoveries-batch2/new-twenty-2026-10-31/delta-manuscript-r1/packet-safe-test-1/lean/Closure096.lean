import Closure095
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node384 : Graph := [[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower384 : ∀ h, Pure node384 h → 11 ≤ h.length := by
  apply indexed_extend node384 [(6, node61)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower61
def node385 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 0, 1, 0], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower385 : ∀ h, Pure node385 h → 11 ≤ h.length := by
  apply indexed_extend node385 [(7, node57)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower57
def node386 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower386 : ∀ h, Pure node386 h → 11 ≤ h.length := by
  apply indexed_extend node386 [(2, node143), (6, node79), (8, node57)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower143
  · exact lower79
  · exact lower57
def node387 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 1, 0]]
theorem lower387 : ∀ h, Pure node387 h → 11 ≤ h.length := by
  apply indexed_extend node387 [(6, node75), (7, node58)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower75
  · exact lower58
def entries96 : List Graph := [node384, node385, node386, node387]
theorem entries_count96 : entries96.length = 4 := by decide +kernel
theorem census_node384 : ((verts node384).filter (wye node384)).length = 1 := by decide +kernel
theorem census_node385 : ((verts node385).filter (wye node385)).length = 1 := by decide +kernel
theorem census_node386 : ((verts node386).filter (wye node386)).length = 3 := by decide +kernel
theorem census_node387 : ((verts node387).filter (wye node387)).length = 2 := by decide +kernel
theorem arc_count96 : (entries96.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by
  simp only [entries96, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node384, census_node385, census_node386, census_node387]
  decide +kernel
end RawCert
