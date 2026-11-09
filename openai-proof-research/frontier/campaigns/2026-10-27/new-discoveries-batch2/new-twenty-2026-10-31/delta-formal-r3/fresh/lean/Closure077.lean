import Closure076
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node308 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]]
theorem lower308 : ∀ h, Pure node308 h → 11 ≤ h.length := by
  apply indexed_extend node308 [(1, node50), (2, node45), (7, node36)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower50
  · exact lower45
  · exact lower36
def node309 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0]]
theorem lower309 : ∀ h, Pure node309 h → 11 ≤ h.length := by
  apply indexed_extend node309 [(2, node46), (5, node66), (8, node36)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower46
  · exact lower66
  · exact lower36
def node310 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 2], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 1, 0, 1, 0]]
theorem lower310 : ∀ h, Pure node310 h → 11 ≤ h.length := by
  apply indexed_extend node310 [(2, node47), (5, node67)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower47
  · exact lower67
def node311 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 1, 0, 1, 0]]
theorem lower311 : ∀ h, Pure node311 h → 11 ≤ h.length := by
  apply indexed_extend node311 [(2, node48), (7, node36)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower48
  · exact lower36
def entries77 : List Graph := [node308, node309, node310, node311]
theorem entries_count77 : entries77.length = 4 := by decide +kernel
theorem census_node308 : ((verts node308).filter (wye node308)).length = 3 := by decide +kernel
theorem census_node309 : ((verts node309).filter (wye node309)).length = 3 := by decide +kernel
theorem census_node310 : ((verts node310).filter (wye node310)).length = 2 := by decide +kernel
theorem census_node311 : ((verts node311).filter (wye node311)).length = 2 := by decide +kernel
theorem arc_count77 : (entries77.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries77, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node308, census_node309, census_node310, census_node311]
  decide +kernel
end RawCert
