import Closure120
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node484 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower484 : ∀ h, Pure node484 h → 11 ≤ h.length := by
  apply indexed_extend node484 [(0, node259), (2, node185), (3, node56), (9, node124)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower259
  · exact lower185
  · exact lower56
  · exact lower124
def node485 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 0]]
theorem lower485 : ∀ h, Pure node485 h → 11 ≤ h.length := by
  apply indexed_extend node485 [(7, node91), (8, node92)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower91
  · exact lower92
def node486 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower486 : ∀ h, Pure node486 h → 11 ≤ h.length := by
  apply indexed_extend node486 [(2, node186), (3, node163), (8, node93)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower186
  · exact lower163
  · exact lower93
def node487 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower487 : ∀ h, Pure node487 h → 11 ≤ h.length := by
  apply indexed_extend node487 [(2, node187), (8, node94)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower187
  · exact lower94
def entries121 : List Graph := [node484, node485, node486, node487]
theorem entries_count121 : entries121.length = 4 := by decide +kernel
theorem census_node484 : ((verts node484).filter (wye node484)).length = 4 := by decide +kernel
theorem census_node485 : ((verts node485).filter (wye node485)).length = 2 := by decide +kernel
theorem census_node486 : ((verts node486).filter (wye node486)).length = 3 := by decide +kernel
theorem census_node487 : ((verts node487).filter (wye node487)).length = 2 := by decide +kernel
theorem arc_count121 : (entries121.map (fun g => ((verts g).filter (wye g)).length)).sum = 11 := by
  simp only [entries121, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node484, census_node485, census_node486, census_node487]
  decide +kernel
end RawCert
