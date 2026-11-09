import Closure157
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node632 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 2, 0, 0]]
theorem lower632 : ∀ h, Pure node632 h → 11 ≤ h.length := by
  apply indexed_extend node632 [(2, node249), (10, node131), (11, node139)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower249
  · exact lower131
  · exact lower139
def node633 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0]]
theorem lower633 : ∀ h, Pure node633 h → 11 ≤ h.length := by
  apply indexed_extend node633 [(9, node135), (11, node133), (12, node132)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower135
  · exact lower133
  · exact lower132
def node634 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 2, 0]]
theorem lower634 : ∀ h, Pure node634 h → 11 ≤ h.length := by
  apply indexed_extend node634 [(9, node136), (11, node134)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower136
  · exact lower134
def node635 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0]]
theorem lower635 : ∀ h, Pure node635 h → 11 ≤ h.length := by
  apply indexed_extend node635 [(11, node138), (12, node137)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower138
  · exact lower137
def entries158 : List Graph := [node632, node633, node634, node635]
theorem entries_count158 : entries158.length = 4 := by decide +kernel
theorem census_node632 : ((verts node632).filter (wye node632)).length = 3 := by decide +kernel
theorem census_node633 : ((verts node633).filter (wye node633)).length = 3 := by decide +kernel
theorem census_node634 : ((verts node634).filter (wye node634)).length = 2 := by decide +kernel
theorem census_node635 : ((verts node635).filter (wye node635)).length = 2 := by decide +kernel
theorem arc_count158 : (entries158.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries158, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node632, census_node633, census_node634, census_node635]
  decide +kernel
end RawCert
