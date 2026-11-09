import Closure174
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node700 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]]
theorem lower700 : ∀ h, Pure node700 h → 11 ≤ h.length := by
  apply indexed_extend node700 [(0, node60), (2, node45), (7, node181), (10, node207)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower60
  · exact lower45
  · exact lower181
  · exact lower207
def node701 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0], [0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower701 : ∀ h, Pure node701 h → 11 ≤ h.length := by
  apply indexed_extend node701 [(0, node75), (5, node193), (7, node180), (10, node212)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower75
  · exact lower193
  · exact lower180
  · exact lower212
def node702 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0]]
theorem lower702 : ∀ h, Pure node702 h → 11 ≤ h.length := by
  apply indexed_extend node702 [(0, node76), (2, node46), (5, node194), (8, node181), (10, node213)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower76
  · exact lower46
  · exact lower194
  · exact lower181
  · exact lower213
def node703 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 2], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 1, 0, 1, 0]]
theorem lower703 : ∀ h, Pure node703 h → 11 ≤ h.length := by
  apply indexed_extend node703 [(0, node77), (2, node47), (5, node195), (6, node180)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower77
  · exact lower47
  · exact lower195
  · exact lower180
def entries175 : List Graph := [node700, node701, node702, node703]
theorem entries_count175 : entries175.length = 4 := by decide +kernel
theorem census_node700 : ((verts node700).filter (wye node700)).length = 4 := by decide +kernel
theorem census_node701 : ((verts node701).filter (wye node701)).length = 4 := by decide +kernel
theorem census_node702 : ((verts node702).filter (wye node702)).length = 5 := by decide +kernel
theorem census_node703 : ((verts node703).filter (wye node703)).length = 4 := by decide +kernel
theorem arc_count175 : (entries175.map (fun g => ((verts g).filter (wye g)).length)).sum = 17 := by
  simp only [entries175, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node700, census_node701, census_node702, census_node703]
  decide +kernel
end RawCert
