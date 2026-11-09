import Closure094
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node380 : Graph := [[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1], [0, 1, 2, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0], [0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 0], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower380 : ∀ h, Pure node380 h → 11 ≤ h.length := by
  apply indexed_extend node380 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node381 : Graph := [[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower381 : ∀ h, Pure node381 h → 11 ≤ h.length := by
  apply indexed_extend node381 [(5, node58), (7, node77)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower58
  · exact lower77
def node382 : Graph := [[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0], [0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower382 : ∀ h, Pure node382 h → 11 ≤ h.length := by
  apply indexed_extend node382 [(6, node60), (7, node78)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower60
  · exact lower78
def node383 : Graph := [[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 2], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower383 : ∀ h, Pure node383 h → 11 ≤ h.length := by
  apply indexed_extend node383 [(5, node59)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower59
def entries95 : List Graph := [node380, node381, node382, node383]
theorem entries_count95 : entries95.length = 4 := by decide +kernel
theorem census_node380 : ((verts node380).filter (wye node380)).length = 0 := by decide +kernel
theorem census_node381 : ((verts node381).filter (wye node381)).length = 2 := by decide +kernel
theorem census_node382 : ((verts node382).filter (wye node382)).length = 2 := by decide +kernel
theorem census_node383 : ((verts node383).filter (wye node383)).length = 1 := by decide +kernel
theorem arc_count95 : (entries95.map (fun g => ((verts g).filter (wye g)).length)).sum = 5 := by
  simp only [entries95, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node380, census_node381, census_node382, census_node383]
  decide +kernel
end RawCert
