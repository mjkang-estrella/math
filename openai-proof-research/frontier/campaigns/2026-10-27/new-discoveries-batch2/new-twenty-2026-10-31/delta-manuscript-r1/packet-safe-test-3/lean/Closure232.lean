import Closure231
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node928 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 1, 2, 0, 1, 0, 0, 1, 0, 0, 1, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower928 : ∀ h, Pure node928 h → 11 ≤ h.length := by
  apply indexed_extend node928 [(3, node268), (9, node261)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower268
  · exact lower261
def node929 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 2], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower929 : ∀ h, Pure node929 h → 11 ≤ h.length := by
  apply indexed_extend node929 [(5, node265)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower265
def node930 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 1, 2, 0, 1, 0, 0, 1, 0, 0, 1, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower930 : ∀ h, Pure node930 h → 11 ≤ h.length := by
  apply indexed_extend node930 [(6, node266)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower266
def node931 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0]]
theorem lower931 : ∀ h, Pure node931 h → 11 ≤ h.length := by
  apply indexed_extend node931 [(5, node263), (8, node260), (9, node261)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower263
  · exact lower260
  · exact lower261
def entries232 : List Graph := [node928, node929, node930, node931]
theorem entries_count232 : entries232.length = 4 := by decide +kernel
theorem census_node928 : ((verts node928).filter (wye node928)).length = 2 := by decide +kernel
theorem census_node929 : ((verts node929).filter (wye node929)).length = 1 := by decide +kernel
theorem census_node930 : ((verts node930).filter (wye node930)).length = 1 := by decide +kernel
theorem census_node931 : ((verts node931).filter (wye node931)).length = 3 := by decide +kernel
theorem arc_count232 : (entries232.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by
  simp only [entries232, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node928, census_node929, census_node930, census_node931]
  decide +kernel
end RawCert
