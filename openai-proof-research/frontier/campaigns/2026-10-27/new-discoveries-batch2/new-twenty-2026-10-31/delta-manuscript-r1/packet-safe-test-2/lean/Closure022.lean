import Closure021
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node88 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0]]
theorem lower88 : ∀ h, Pure node88 h → 11 ≤ h.length := by
  apply indexed_extend node88 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node89 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3], [2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0]]
theorem lower89 : ∀ h, Pure node89 h → 11 ≤ h.length := by
  apply indexed_extend node89 [(0, node22), (5, node6)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower22
  · exact lower6
def node90 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1], [0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 3, 1, 0, 0]]
theorem lower90 : ∀ h, Pure node90 h → 11 ≤ h.length := by
  apply indexed_extend node90 [(0, node24)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower24
def node91 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0]]
theorem lower91 : ∀ h, Pure node91 h → 11 ≤ h.length := by
  apply indexed_extend node91 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries22 : List Graph := [node88, node89, node90, node91]
theorem entries_count22 : entries22.length = 4 := by decide +kernel
theorem census_node88 : ((verts node88).filter (wye node88)).length = 0 := by decide +kernel
theorem census_node89 : ((verts node89).filter (wye node89)).length = 2 := by decide +kernel
theorem census_node90 : ((verts node90).filter (wye node90)).length = 1 := by decide +kernel
theorem census_node91 : ((verts node91).filter (wye node91)).length = 0 := by decide +kernel
theorem arc_count22 : (entries22.map (fun g => ((verts g).filter (wye g)).length)).sum = 3 := by
  simp only [entries22, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node88, census_node89, census_node90, census_node91]
  decide +kernel
end RawCert
