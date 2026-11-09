import Closure057
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node232 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0]]
theorem lower232 : ∀ h, Pure node232 h → 11 ≤ h.length := by
  apply indexed_extend node232 [(6, node21)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower21
def node233 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 1, 0, 2, 1, 0]]
theorem lower233 : ∀ h, Pure node233 h → 11 ≤ h.length := by
  apply indexed_extend node233 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node234 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 1, 0]]
theorem lower234 : ∀ h, Pure node234 h → 11 ≤ h.length := by
  apply indexed_extend node234 [(5, node20), (6, node21)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower20
  · exact lower21
def node235 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0]]
theorem lower235 : ∀ h, Pure node235 h → 11 ≤ h.length := by
  apply indexed_extend node235 [(4, node19)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower19
def entries58 : List Graph := [node232, node233, node234, node235]
theorem entries_count58 : entries58.length = 4 := by decide +kernel
theorem census_node232 : ((verts node232).filter (wye node232)).length = 1 := by decide +kernel
theorem census_node233 : ((verts node233).filter (wye node233)).length = 0 := by decide +kernel
theorem census_node234 : ((verts node234).filter (wye node234)).length = 2 := by decide +kernel
theorem census_node235 : ((verts node235).filter (wye node235)).length = 1 := by decide +kernel
theorem arc_count58 : (entries58.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by
  simp only [entries58, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node232, census_node233, census_node234, census_node235]
  decide +kernel
end RawCert
