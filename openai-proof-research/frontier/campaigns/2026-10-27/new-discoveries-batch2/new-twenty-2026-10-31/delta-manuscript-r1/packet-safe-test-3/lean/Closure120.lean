import Closure119
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node480 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 2, 0]]
theorem lower480 : ∀ h, Pure node480 h → 11 ≤ h.length := by
  apply indexed_extend node480 [(0, node271), (3, node51), (10, node122)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower271
  · exact lower51
  · exact lower122
def node481 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 2], [0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower481 : ∀ h, Pure node481 h → 11 ≤ h.length := by
  apply indexed_extend node481 [(0, node281), (12, node90)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower281
  · exact lower90
def node482 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0]]
theorem lower482 : ∀ h, Pure node482 h → 11 ≤ h.length := by
  apply indexed_extend node482 [(0, node282), (3, node52), (10, node126)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower282
  · exact lower52
  · exact lower126
def node483 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 0, 0, 1, 0, 2, 2, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower483 : ∀ h, Pure node483 h → 11 ≤ h.length := by
  apply indexed_extend node483 [(0, node258), (2, node184)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower258
  · exact lower184
def entries120 : List Graph := [node480, node481, node482, node483]
theorem entries_count120 : entries120.length = 4 := by decide +kernel
theorem census_node480 : ((verts node480).filter (wye node480)).length = 3 := by decide +kernel
theorem census_node481 : ((verts node481).filter (wye node481)).length = 2 := by decide +kernel
theorem census_node482 : ((verts node482).filter (wye node482)).length = 3 := by decide +kernel
theorem census_node483 : ((verts node483).filter (wye node483)).length = 2 := by decide +kernel
theorem arc_count120 : (entries120.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries120, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node480, census_node481, census_node482, census_node483]
  decide +kernel
end RawCert
