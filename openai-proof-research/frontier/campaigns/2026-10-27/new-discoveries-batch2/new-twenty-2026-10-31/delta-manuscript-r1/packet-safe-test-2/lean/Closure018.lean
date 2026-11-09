import Closure017
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node72 : Graph := [[0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [0, 2, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0], [1, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower72 : ∀ h, Pure node72 h → 11 ≤ h.length := by
  apply indexed_extend node72 [(1, node11), (11, node3)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower11
  · exact lower3
def node73 : Graph := [[0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [0, 2, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0], [1, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower73 : ∀ h, Pure node73 h → 11 ≤ h.length := by
  apply indexed_extend node73 [(11, node3)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower3
def node74 : Graph := [[0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1], [0, 2, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower74 : ∀ h, Pure node74 h → 11 ≤ h.length := by
  apply indexed_extend node74 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node75 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0], [0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0], [1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower75 : ∀ h, Pure node75 h → 11 ≤ h.length := by
  apply indexed_extend node75 [(6, node4)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower4
def entries18 : List Graph := [node72, node73, node74, node75]
theorem entries_count18 : entries18.length = 4 := by decide +kernel
theorem census_node72 : ((verts node72).filter (wye node72)).length = 2 := by decide +kernel
theorem census_node73 : ((verts node73).filter (wye node73)).length = 1 := by decide +kernel
theorem census_node74 : ((verts node74).filter (wye node74)).length = 0 := by decide +kernel
theorem census_node75 : ((verts node75).filter (wye node75)).length = 1 := by decide +kernel
theorem arc_count18 : (entries18.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by
  simp only [entries18, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node72, census_node73, census_node74, census_node75]
  decide +kernel
end RawCert
