import Closure013
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node56 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 3, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 1, 1], [2, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower56 : ∀ h, Pure node56 h → 11 ≤ h.length := by
  apply indexed_extend node56 [(2, node7)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower7
def node57 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower57 : ∀ h, Pure node57 h → 11 ≤ h.length := by
  apply indexed_extend node57 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node58 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower58 : ∀ h, Pure node58 h → 11 ≤ h.length := by
  apply indexed_extend node58 [(6, node4)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower4
def node59 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 2], [2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower59 : ∀ h, Pure node59 h → 11 ≤ h.length := by
  apply indexed_extend node59 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries14 : List Graph := [node56, node57, node58, node59]
theorem entries_count14 : entries14.length = 4 := by decide +kernel
theorem census_node56 : ((verts node56).filter (wye node56)).length = 1 := by decide +kernel
theorem census_node57 : ((verts node57).filter (wye node57)).length = 0 := by decide +kernel
theorem census_node58 : ((verts node58).filter (wye node58)).length = 1 := by decide +kernel
theorem census_node59 : ((verts node59).filter (wye node59)).length = 0 := by decide +kernel
theorem arc_count14 : (entries14.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by
  simp only [entries14, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node56, census_node57, census_node58, census_node59]
  decide +kernel
end RawCert
