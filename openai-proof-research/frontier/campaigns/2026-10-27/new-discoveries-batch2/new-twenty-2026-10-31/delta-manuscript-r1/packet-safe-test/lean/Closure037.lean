import Closure036
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node148 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0]]
theorem lower148 : ∀ h, Pure node148 h → 11 ≤ h.length := by
  apply indexed_extend node148 [(5, node9)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower9
def node149 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower149 : ∀ h, Pure node149 h → 11 ≤ h.length := by
  apply indexed_extend node149 [(5, node9), (6, node10)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower9
  · exact lower10
def node150 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1], [1, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower150 : ∀ h, Pure node150 h → 11 ≤ h.length := by
  apply indexed_extend node150 [(3, node11)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower11
def node151 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [1, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower151 : ∀ h, Pure node151 h → 11 ≤ h.length := by
  apply indexed_extend node151 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries37 : List Graph := [node148, node149, node150, node151]
theorem entries_count37 : entries37.length = 4 := by decide +kernel
theorem census_node148 : ((verts node148).filter (wye node148)).length = 1 := by decide +kernel
theorem census_node149 : ((verts node149).filter (wye node149)).length = 2 := by decide +kernel
theorem census_node150 : ((verts node150).filter (wye node150)).length = 1 := by decide +kernel
theorem census_node151 : ((verts node151).filter (wye node151)).length = 0 := by decide +kernel
theorem arc_count37 : (entries37.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by
  simp only [entries37, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node148, census_node149, census_node150, census_node151]
  decide +kernel
end RawCert
