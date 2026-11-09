import Closure162
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node652 : Graph := [[0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0], [0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower652 : ∀ h, Pure node652 h → 11 ≤ h.length := by
  apply indexed_extend node652 [(5, node176), (8, node145)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower176
  · exact lower145
def node653 : Graph := [[0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower653 : ∀ h, Pure node653 h → 11 ≤ h.length := by
  apply indexed_extend node653 [(7, node146)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower146
def node654 : Graph := [[0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 1, 0]]
theorem lower654 : ∀ h, Pure node654 h → 11 ≤ h.length := by
  apply indexed_extend node654 [(5, node148), (6, node149), (7, node147)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower148
  · exact lower149
  · exact lower147
def node655 : Graph := [[0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower655 : ∀ h, Pure node655 h → 11 ≤ h.length := by
  apply indexed_extend node655 [(3, node162), (7, node150)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower162
  · exact lower150
def entries163 : List Graph := [node652, node653, node654, node655]
theorem entries_count163 : entries163.length = 4 := by decide +kernel
theorem census_node652 : ((verts node652).filter (wye node652)).length = 2 := by decide +kernel
theorem census_node653 : ((verts node653).filter (wye node653)).length = 1 := by decide +kernel
theorem census_node654 : ((verts node654).filter (wye node654)).length = 3 := by decide +kernel
theorem census_node655 : ((verts node655).filter (wye node655)).length = 2 := by decide +kernel
theorem arc_count163 : (entries163.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by
  simp only [entries163, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node652, census_node653, census_node654, census_node655]
  decide +kernel
end RawCert
