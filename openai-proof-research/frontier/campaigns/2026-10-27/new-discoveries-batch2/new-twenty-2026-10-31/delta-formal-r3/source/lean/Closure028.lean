import Closure027
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node112 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 1, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2], [1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 1, 2, 0, 0]]
theorem lower112 : ∀ h, Pure node112 h → 11 ≤ h.length := by
  apply indexed_extend node112 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node113 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 1, 1, 0], [0, 2, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0], [1, 0, 0, 1, 1, 2, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower113 : ∀ h, Pure node113 h → 11 ≤ h.length := by
  apply indexed_extend node113 [(1, node15), (11, node6)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower15
  · exact lower6
def node114 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 2], [1, 0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 2, 0, 1, 0, 1, 0]]
theorem lower114 : ∀ h, Pure node114 h → 11 ≤ h.length := by
  apply indexed_extend node114 [(2, node16)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower16
def node115 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0], [1, 0, 0, 1, 1, 2, 0, 0, 0, 1, 0, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower115 : ∀ h, Pure node115 h → 11 ≤ h.length := by
  apply indexed_extend node115 [(11, node6)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower6
def entries28 : List Graph := [node112, node113, node114, node115]
theorem entries_count28 : entries28.length = 4 := by decide +kernel
theorem census_node112 : ((verts node112).filter (wye node112)).length = 0 := by decide +kernel
theorem census_node113 : ((verts node113).filter (wye node113)).length = 2 := by decide +kernel
theorem census_node114 : ((verts node114).filter (wye node114)).length = 1 := by decide +kernel
theorem census_node115 : ((verts node115).filter (wye node115)).length = 1 := by decide +kernel
theorem arc_count28 : (entries28.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by
  simp only [entries28, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node112, census_node113, census_node114, census_node115]
  decide +kernel
end RawCert
