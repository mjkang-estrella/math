import Closure096
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node388 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 0, 1, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower388 : ∀ h, Pure node388 h → 11 ≤ h.length := by
  apply indexed_extend node388 [(7, node59)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower59
def node389 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower389 : ∀ h, Pure node389 h → 11 ≤ h.length := by
  apply indexed_extend node389 [(6, node80), (9, node58)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower80
  · exact lower58
def node390 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower390 : ∀ h, Pure node390 h → 11 ≤ h.length := by
  apply indexed_extend node390 [(2, node144), (6, node81), (8, node59), (10, node58)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower144
  · exact lower81
  · exact lower59
  · exact lower58
def node391 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower391 : ∀ h, Pure node391 h → 11 ≤ h.length := by
  apply indexed_extend node391 [(8, node59), (12, node57)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower59
  · exact lower57
def entries97 : List Graph := [node388, node389, node390, node391]
theorem entries_count97 : entries97.length = 4 := by decide +kernel
theorem census_node388 : ((verts node388).filter (wye node388)).length = 1 := by decide +kernel
theorem census_node389 : ((verts node389).filter (wye node389)).length = 2 := by decide +kernel
theorem census_node390 : ((verts node390).filter (wye node390)).length = 4 := by decide +kernel
theorem census_node391 : ((verts node391).filter (wye node391)).length = 2 := by decide +kernel
theorem arc_count97 : (entries97.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries97, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node388, census_node389, census_node390, census_node391]
  decide +kernel
end RawCert
