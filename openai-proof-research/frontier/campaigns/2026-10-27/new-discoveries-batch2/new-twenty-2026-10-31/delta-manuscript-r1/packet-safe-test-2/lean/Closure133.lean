import Closure132
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node532 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 1], [1, 0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 2, 0, 0]]
theorem lower532 : ∀ h, Pure node532 h → 11 ≤ h.length := by
  apply indexed_extend node532 [(3, node64), (11, node139)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower64
  · exact lower139
def node533 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 2], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0]]
theorem lower533 : ∀ h, Pure node533 h → 11 ≤ h.length := by
  apply indexed_extend node533 [(3, node65), (6, node112)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower65
  · exact lower112
def node534 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0], [1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower534 : ∀ h, Pure node534 h → 11 ≤ h.length := by
  apply indexed_extend node534 [(1, node189), (3, node72), (5, node113), (12, node99)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower189
  · exact lower72
  · exact lower113
  · exact lower99
def node535 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower535 : ∀ h, Pure node535 h → 11 ≤ h.length := by
  apply indexed_extend node535 [(1, node196), (2, node191), (5, node113), (12, node100)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower196
  · exact lower191
  · exact lower113
  · exact lower100
def entries133 : List Graph := [node532, node533, node534, node535]
theorem entries_count133 : entries133.length = 4 := by decide +kernel
theorem census_node532 : ((verts node532).filter (wye node532)).length = 2 := by decide +kernel
theorem census_node533 : ((verts node533).filter (wye node533)).length = 2 := by decide +kernel
theorem census_node534 : ((verts node534).filter (wye node534)).length = 4 := by decide +kernel
theorem census_node535 : ((verts node535).filter (wye node535)).length = 4 := by decide +kernel
theorem arc_count133 : (entries133.map (fun g => ((verts g).filter (wye g)).length)).sum = 12 := by
  simp only [entries133, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node532, census_node533, census_node534, census_node535]
  decide +kernel
end RawCert
