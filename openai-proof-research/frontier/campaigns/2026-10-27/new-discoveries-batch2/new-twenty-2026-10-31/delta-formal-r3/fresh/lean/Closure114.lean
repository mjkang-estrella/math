import Closure113
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node456 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]]
theorem lower456 : ∀ h, Pure node456 h → 11 ≤ h.length := by
  apply indexed_extend node456 [(8, node87)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower87
def node457 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0], [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0]]
theorem lower457 : ∀ h, Pure node457 h → 11 ≤ h.length := by
  apply indexed_extend node457 [(3, node32), (9, node87)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower32
  · exact lower87
def node458 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower458 : ∀ h, Pure node458 h → 11 ≤ h.length := by
  apply indexed_extend node458 [(2, node179), (8, node88), (10, node87)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower179
  · exact lower88
  · exact lower87
def node459 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower459 : ∀ h, Pure node459 h → 11 ≤ h.length := by
  apply indexed_extend node459 [(8, node88)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower88
def entries114 : List Graph := [node456, node457, node458, node459]
theorem entries_count114 : entries114.length = 4 := by decide +kernel
theorem census_node456 : ((verts node456).filter (wye node456)).length = 1 := by decide +kernel
theorem census_node457 : ((verts node457).filter (wye node457)).length = 2 := by decide +kernel
theorem census_node458 : ((verts node458).filter (wye node458)).length = 3 := by decide +kernel
theorem census_node459 : ((verts node459).filter (wye node459)).length = 1 := by decide +kernel
theorem arc_count114 : (entries114.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by
  simp only [entries114, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node456, census_node457, census_node458, census_node459]
  decide +kernel
end RawCert
