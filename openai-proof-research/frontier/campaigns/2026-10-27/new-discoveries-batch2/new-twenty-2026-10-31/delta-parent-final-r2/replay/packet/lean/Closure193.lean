import Closure192
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node772 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 1], [1, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 1, 1, 0, 1, 2, 0, 0, 0]]
theorem lower772 : ∀ h, Pure node772 h → 11 ≤ h.length := by
  apply indexed_extend node772 [(2, node158), (9, node194), (10, node249)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower158
  · exact lower194
  · exact lower249
def node773 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0]]
theorem lower773 : ∀ h, Pure node773 h → 11 ≤ h.length := by
  apply indexed_extend node773 [(2, node159), (5, node203), (9, node195)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower159
  · exact lower203
  · exact lower195
def node774 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 1, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 1], [1, 0, 1, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower774 : ∀ h, Pure node774 h → 11 ≤ h.length := by
  apply indexed_extend node774 [(4, node200), (8, node196)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower200
  · exact lower196
def node775 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1, 0], [1, 0, 1, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower775 : ∀ h, Pure node775 h → 11 ≤ h.length := by
  apply indexed_extend node775 [(4, node201), (9, node197)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower201
  · exact lower197
def entries193 : List Graph := [node772, node773, node774, node775]
theorem entries_count193 : entries193.length = 4 := by decide +kernel
theorem census_node772 : ((verts node772).filter (wye node772)).length = 3 := by decide +kernel
theorem census_node773 : ((verts node773).filter (wye node773)).length = 3 := by decide +kernel
theorem census_node774 : ((verts node774).filter (wye node774)).length = 2 := by decide +kernel
theorem census_node775 : ((verts node775).filter (wye node775)).length = 2 := by decide +kernel
theorem arc_count193 : (entries193.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries193, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node772, census_node773, census_node774, census_node775]
  decide +kernel
end RawCert
