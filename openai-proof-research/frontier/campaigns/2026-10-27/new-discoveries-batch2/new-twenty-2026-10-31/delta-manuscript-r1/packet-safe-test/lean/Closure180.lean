import Closure179
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node720 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower720 : ∀ h, Pure node720 h → 11 ≤ h.length := by
  apply indexed_extend node720 [(0, node28), (3, node206), (4, node200), (8, node182)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower28
  · exact lower206
  · exact lower200
  · exact lower182
def node721 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower721 : ∀ h, Pure node721 h → 11 ≤ h.length := by
  apply indexed_extend node721 [(0, node31), (4, node201)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower31
  · exact lower201
def node722 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1, 1, 2, 0, 0, 0]]
theorem lower722 : ∀ h, Pure node722 h → 11 ≤ h.length := by
  apply indexed_extend node722 [(0, node32), (2, node95), (10, node218)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower32
  · exact lower95
  · exact lower218
def node723 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower723 : ∀ h, Pure node723 h → 11 ≤ h.length := by
  apply indexed_extend node723 [(0, node143), (6, node183)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower143
  · exact lower183
def entries180 : List Graph := [node720, node721, node722, node723]
theorem entries_count180 : entries180.length = 4 := by decide +kernel
theorem census_node720 : ((verts node720).filter (wye node720)).length = 4 := by decide +kernel
theorem census_node721 : ((verts node721).filter (wye node721)).length = 2 := by decide +kernel
theorem census_node722 : ((verts node722).filter (wye node722)).length = 3 := by decide +kernel
theorem census_node723 : ((verts node723).filter (wye node723)).length = 2 := by decide +kernel
theorem arc_count180 : (entries180.map (fun g => ((verts g).filter (wye g)).length)).sum = 11 := by
  simp only [entries180, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node720, census_node721, census_node722, census_node723]
  decide +kernel
end RawCert
