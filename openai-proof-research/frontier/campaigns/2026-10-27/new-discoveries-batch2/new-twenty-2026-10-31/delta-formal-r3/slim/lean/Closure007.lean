import Closure006
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node28 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower28 : ∀ h, Pure node28 h → 11 ≤ h.length := by
  apply indexed_extend node28 [(2, node1), (7, node0)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower1
  · exact lower0
def node29 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 3, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower29 : ∀ h, Pure node29 h → 11 ≤ h.length := by
  apply indexed_extend node29 [(3, node1)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower1
def node30 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0], [0, 2, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 3, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower30 : ∀ h, Pure node30 h → 11 ≤ h.length := by
  apply indexed_extend node30 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node31 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower31 : ∀ h, Pure node31 h → 11 ≤ h.length := by
  apply indexed_extend node31 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries7 : List Graph := [node28, node29, node30, node31]
theorem entries_count7 : entries7.length = 4 := by decide +kernel
theorem census_node28 : ((verts node28).filter (wye node28)).length = 2 := by decide +kernel
theorem census_node29 : ((verts node29).filter (wye node29)).length = 1 := by decide +kernel
theorem census_node30 : ((verts node30).filter (wye node30)).length = 0 := by decide +kernel
theorem census_node31 : ((verts node31).filter (wye node31)).length = 0 := by decide +kernel
theorem arc_count7 : (entries7.map (fun g => ((verts g).filter (wye g)).length)).sum = 3 := by
  simp only [entries7, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node28, census_node29, census_node30, census_node31]
  decide +kernel
end RawCert
