import Closure432
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1732 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower1732 : ∀ h, Pure node1732 h → 11 ≤ h.length := by
  apply indexed_extend node1732 [(3, node954), (4, node949), (7, node965), (9, node941), (12, node935)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower954
  · exact lower949
  · exact lower965
  · exact lower941
  · exact lower935
def node1733 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower1733 : ∀ h, Pure node1733 h → 11 ≤ h.length := by
  apply indexed_extend node1733 [(4, node950), (9, node941)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower950
  · exact lower941
def node1734 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1734 : ∀ h, Pure node1734 h → 11 ≤ h.length := by
  apply indexed_extend node1734 [(3, node951), (5, node953), (7, node969), (13, node936)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower951
  · exact lower953
  · exact lower969
  · exact lower936
def node1735 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1735 : ∀ h, Pure node1735 h → 11 ≤ h.length := by
  apply indexed_extend node1735 [(3, node952), (6, node954), (7, node970), (13, node937)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower952
  · exact lower954
  · exact lower970
  · exact lower937
def entries433 : List Graph := [node1732, node1733, node1734, node1735]
theorem entries_count433 : entries433.length = 4 := by decide +kernel
theorem census_node1732 : ((verts node1732).filter (wye node1732)).length = 5 := by decide +kernel
theorem census_node1733 : ((verts node1733).filter (wye node1733)).length = 2 := by decide +kernel
theorem census_node1734 : ((verts node1734).filter (wye node1734)).length = 4 := by decide +kernel
theorem census_node1735 : ((verts node1735).filter (wye node1735)).length = 4 := by decide +kernel
theorem arc_count433 : (entries433.map (fun g => ((verts g).filter (wye g)).length)).sum = 15 := by
  simp only [entries433, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1732, census_node1733, census_node1734, census_node1735]
  decide +kernel
end RawCert
