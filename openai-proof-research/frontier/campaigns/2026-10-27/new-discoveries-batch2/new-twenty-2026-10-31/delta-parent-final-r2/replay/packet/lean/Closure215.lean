import Closure214
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node860 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower860 : ∀ h, Pure node860 h → 11 ≤ h.length := by
  apply indexed_extend node860 [(4, node243), (5, node244), (12, node228)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower243
  · exact lower244
  · exact lower228
def node861 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower861 : ∀ h, Pure node861 h → 11 ≤ h.length := by
  apply indexed_extend node861 [(6, node245), (9, node229)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower245
  · exact lower229
def node862 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower862 : ∀ h, Pure node862 h → 11 ≤ h.length := by
  apply indexed_extend node862 [(6, node246), (9, node231), (10, node230)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower246
  · exact lower231
  · exact lower230
def node863 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower863 : ∀ h, Pure node863 h → 11 ≤ h.length := by
  apply indexed_extend node863 [(6, node247), (10, node230)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower247
  · exact lower230
def entries215 : List Graph := [node860, node861, node862, node863]
theorem entries_count215 : entries215.length = 4 := by decide +kernel
theorem census_node860 : ((verts node860).filter (wye node860)).length = 3 := by decide +kernel
theorem census_node861 : ((verts node861).filter (wye node861)).length = 2 := by decide +kernel
theorem census_node862 : ((verts node862).filter (wye node862)).length = 3 := by decide +kernel
theorem census_node863 : ((verts node863).filter (wye node863)).length = 2 := by decide +kernel
theorem arc_count215 : (entries215.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries215, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node860, census_node861, census_node862, census_node863]
  decide +kernel
end RawCert
