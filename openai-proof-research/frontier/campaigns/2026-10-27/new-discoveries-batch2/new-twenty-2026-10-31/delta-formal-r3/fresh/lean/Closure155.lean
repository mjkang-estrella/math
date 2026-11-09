import Closure154
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node620 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0]]
theorem lower620 : ∀ h, Pure node620 h → 11 ≤ h.length := by
  apply indexed_extend node620 [(5, node136)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower136
def node621 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0]]
theorem lower621 : ∀ h, Pure node621 h → 11 ≤ h.length := by
  apply indexed_extend node621 [(6, node137)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower137
def node622 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0]]
theorem lower622 : ∀ h, Pure node622 h → 11 ≤ h.length := by
  apply indexed_extend node622 [(6, node138), (7, node139)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower138
  · exact lower139
def node623 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower623 : ∀ h, Pure node623 h → 11 ≤ h.length := by
  apply indexed_extend node623 [(1, node240), (9, node129), (12, node132)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower240
  · exact lower129
  · exact lower132
def entries155 : List Graph := [node620, node621, node622, node623]
theorem entries_count155 : entries155.length = 4 := by decide +kernel
theorem census_node620 : ((verts node620).filter (wye node620)).length = 1 := by decide +kernel
theorem census_node621 : ((verts node621).filter (wye node621)).length = 1 := by decide +kernel
theorem census_node622 : ((verts node622).filter (wye node622)).length = 2 := by decide +kernel
theorem census_node623 : ((verts node623).filter (wye node623)).length = 3 := by decide +kernel
theorem arc_count155 : (entries155.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by
  simp only [entries155, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node620, census_node621, census_node622, census_node623]
  decide +kernel
end RawCert
