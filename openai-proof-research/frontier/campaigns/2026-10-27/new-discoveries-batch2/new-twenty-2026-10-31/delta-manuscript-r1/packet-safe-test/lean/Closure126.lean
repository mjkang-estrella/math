import Closure125
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node504 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 0, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [1, 0, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0], [0, 1, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0]]
theorem lower504 : ∀ h, Pure node504 h → 11 ≤ h.length := by
  apply indexed_extend node504 [(5, node101), (8, node100), (11, node128)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower101
  · exact lower100
  · exact lower128
def node505 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower505 : ∀ h, Pure node505 h → 11 ≤ h.length := by
  apply indexed_extend node505 [(3, node166), (12, node93)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower166
  · exact lower93
def node506 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower506 : ∀ h, Pure node506 h → 11 ≤ h.length := by
  apply indexed_extend node506 [(5, node102), (12, node94)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower102
  · exact lower94
def node507 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower507 : ∀ h, Pure node507 h → 11 ≤ h.length := by
  apply indexed_extend node507 [(2, node188), (7, node102), (10, node95)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower188
  · exact lower102
  · exact lower95
def entries126 : List Graph := [node504, node505, node506, node507]
theorem entries_count126 : entries126.length = 4 := by decide +kernel
theorem census_node504 : ((verts node504).filter (wye node504)).length = 3 := by decide +kernel
theorem census_node505 : ((verts node505).filter (wye node505)).length = 2 := by decide +kernel
theorem census_node506 : ((verts node506).filter (wye node506)).length = 2 := by decide +kernel
theorem census_node507 : ((verts node507).filter (wye node507)).length = 3 := by decide +kernel
theorem arc_count126 : (entries126.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries126, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node504, census_node505, census_node506, census_node507]
  decide +kernel
end RawCert
