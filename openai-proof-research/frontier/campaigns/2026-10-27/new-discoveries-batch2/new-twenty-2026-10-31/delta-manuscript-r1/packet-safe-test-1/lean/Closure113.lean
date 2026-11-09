import Closure112
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node452 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 0, 1, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower452 : ∀ h, Pure node452 h → 11 ≤ h.length := by
  apply indexed_extend node452 [(7, node86)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower86
def node453 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2], [1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower453 : ∀ h, Pure node453 h → 11 ≤ h.length := by
  apply indexed_extend node453 [(3, node31), (9, node85)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower31
  · exact lower85
def node454 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower454 : ∀ h, Pure node454 h → 11 ≤ h.length := by
  apply indexed_extend node454 [(2, node178), (8, node86), (10, node85)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower178
  · exact lower86
  · exact lower85
def node455 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower455 : ∀ h, Pure node455 h → 11 ≤ h.length := by
  apply indexed_extend node455 [(3, node33), (8, node86), (12, node84)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower33
  · exact lower86
  · exact lower84
def entries113 : List Graph := [node452, node453, node454, node455]
theorem entries_count113 : entries113.length = 4 := by decide +kernel
theorem census_node452 : ((verts node452).filter (wye node452)).length = 1 := by decide +kernel
theorem census_node453 : ((verts node453).filter (wye node453)).length = 2 := by decide +kernel
theorem census_node454 : ((verts node454).filter (wye node454)).length = 3 := by decide +kernel
theorem census_node455 : ((verts node455).filter (wye node455)).length = 3 := by decide +kernel
theorem arc_count113 : (entries113.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries113, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node452, census_node453, census_node454, census_node455]
  decide +kernel
end RawCert
