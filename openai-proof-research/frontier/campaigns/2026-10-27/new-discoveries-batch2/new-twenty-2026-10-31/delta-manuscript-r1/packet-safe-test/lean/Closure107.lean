import Closure106
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node428 : Graph := [[0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 2, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower428 : ∀ h, Pure node428 h → 11 ≤ h.length := by
  apply indexed_extend node428 [(1, node167), (11, node74)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower167
  · exact lower74
def node429 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower429 : ∀ h, Pure node429 h → 11 ≤ h.length := by
  apply indexed_extend node429 [(5, node75), (6, node76), (7, node77), (8, node78)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower75
  · exact lower76
  · exact lower77
  · exact lower78
def node430 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower430 : ∀ h, Pure node430 h → 11 ≤ h.length := by
  apply indexed_extend node430 [(2, node168), (6, node79)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower168
  · exact lower79
def node431 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower431 : ∀ h, Pure node431 h → 11 ≤ h.length := by
  apply indexed_extend node431 [(2, node169), (5, node79)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower169
  · exact lower79
def entries107 : List Graph := [node428, node429, node430, node431]
theorem entries_count107 : entries107.length = 4 := by decide +kernel
theorem census_node428 : ((verts node428).filter (wye node428)).length = 2 := by decide +kernel
theorem census_node429 : ((verts node429).filter (wye node429)).length = 4 := by decide +kernel
theorem census_node430 : ((verts node430).filter (wye node430)).length = 2 := by decide +kernel
theorem census_node431 : ((verts node431).filter (wye node431)).length = 2 := by decide +kernel
theorem arc_count107 : (entries107.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries107, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node428, census_node429, census_node430, census_node431]
  decide +kernel
end RawCert
