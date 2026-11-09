import Closure171
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node688 : Graph := [[0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0], [0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower688 : ∀ h, Pure node688 h → 11 ≤ h.length := by
  apply indexed_extend node688 [(5, node176), (8, node174), (12, node170)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower176
  · exact lower174
  · exact lower170
def node689 : Graph := [[0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower689 : ∀ h, Pure node689 h → 11 ≤ h.length := by
  apply indexed_extend node689 [(2, node29), (4, node177)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower29
  · exact lower177
def node690 : Graph := [[0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0], [0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower690 : ∀ h, Pure node690 h → 11 ≤ h.length := by
  apply indexed_extend node690 [(2, node30)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower30
def node691 : Graph := [[0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower691 : ∀ h, Pure node691 h → 11 ≤ h.length := by
  apply indexed_extend node691 [(4, node178)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower178
def entries172 : List Graph := [node688, node689, node690, node691]
theorem entries_count172 : entries172.length = 4 := by decide +kernel
theorem census_node688 : ((verts node688).filter (wye node688)).length = 3 := by decide +kernel
theorem census_node689 : ((verts node689).filter (wye node689)).length = 2 := by decide +kernel
theorem census_node690 : ((verts node690).filter (wye node690)).length = 1 := by decide +kernel
theorem census_node691 : ((verts node691).filter (wye node691)).length = 1 := by decide +kernel
theorem arc_count172 : (entries172.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by
  simp only [entries172, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node688, census_node689, census_node690, census_node691]
  decide +kernel
end RawCert
