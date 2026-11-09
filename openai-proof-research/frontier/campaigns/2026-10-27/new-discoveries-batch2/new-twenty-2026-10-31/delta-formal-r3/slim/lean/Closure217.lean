import Closure216
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node868 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower868 : ∀ h, Pure node868 h → 11 ≤ h.length := by
  apply indexed_extend node868 [(5, node245)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower245
def node869 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower869 : ∀ h, Pure node869 h → 11 ≤ h.length := by
  apply indexed_extend node869 [(5, node246), (6, node248), (10, node234)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower246
  · exact lower248
  · exact lower234
def node870 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower870 : ∀ h, Pure node870 h → 11 ≤ h.length := by
  apply indexed_extend node870 [(5, node247), (6, node249), (10, node234)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower247
  · exact lower249
  · exact lower234
def node871 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0]]
theorem lower871 : ∀ h, Pure node871 h → 11 ≤ h.length := by
  apply indexed_extend node871 [(4, node240), (9, node235)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower240
  · exact lower235
def entries217 : List Graph := [node868, node869, node870, node871]
theorem entries_count217 : entries217.length = 4 := by decide +kernel
theorem census_node868 : ((verts node868).filter (wye node868)).length = 1 := by decide +kernel
theorem census_node869 : ((verts node869).filter (wye node869)).length = 3 := by decide +kernel
theorem census_node870 : ((verts node870).filter (wye node870)).length = 3 := by decide +kernel
theorem census_node871 : ((verts node871).filter (wye node871)).length = 2 := by decide +kernel
theorem arc_count217 : (entries217.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries217, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node868, census_node869, census_node870, census_node871]
  decide +kernel
end RawCert
