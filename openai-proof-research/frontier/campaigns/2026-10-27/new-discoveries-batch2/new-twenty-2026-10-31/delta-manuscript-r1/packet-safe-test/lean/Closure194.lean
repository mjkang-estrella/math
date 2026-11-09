import Closure193
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node776 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0], [1, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower776 : ∀ h, Pure node776 h → 11 ≤ h.length := by
  apply indexed_extend node776 [(2, node166), (4, node204), (12, node189)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower166
  · exact lower204
  · exact lower189
def node777 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower777 : ∀ h, Pure node777 h → 11 ≤ h.length := by
  apply indexed_extend node777 [(6, node204), (9, node243), (12, node190)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower204
  · exact lower243
  · exact lower190
def node778 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower778 : ∀ h, Pure node778 h → 11 ≤ h.length := by
  apply indexed_extend node778 [(2, node167), (9, node244)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower167
  · exact lower244
def node779 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower779 : ∀ h, Pure node779 h → 11 ≤ h.length := by
  apply indexed_extend node779 [(6, node205), (8, node198), (10, node192)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower205
  · exact lower198
  · exact lower192
def entries194 : List Graph := [node776, node777, node778, node779]
theorem entries_count194 : entries194.length = 4 := by decide +kernel
theorem census_node776 : ((verts node776).filter (wye node776)).length = 3 := by decide +kernel
theorem census_node777 : ((verts node777).filter (wye node777)).length = 3 := by decide +kernel
theorem census_node778 : ((verts node778).filter (wye node778)).length = 2 := by decide +kernel
theorem census_node779 : ((verts node779).filter (wye node779)).length = 3 := by decide +kernel
theorem arc_count194 : (entries194.map (fun g => ((verts g).filter (wye g)).length)).sum = 11 := by
  simp only [entries194, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node776, census_node777, census_node778, census_node779]
  decide +kernel
end RawCert
