import Closure020
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node84 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0], [1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower84 : ∀ h, Pure node84 h → 11 ≤ h.length := by
  apply indexed_extend node84 [(3, node0)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower0
def node85 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2], [1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower85 : ∀ h, Pure node85 h → 11 ≤ h.length := by
  apply indexed_extend node85 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node86 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 2], [1, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0], [0, 1, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower86 : ∀ h, Pure node86 h → 11 ≤ h.length := by
  apply indexed_extend node86 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node87 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0], [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]]
theorem lower87 : ∀ h, Pure node87 h → 11 ≤ h.length := by
  apply indexed_extend node87 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries21 : List Graph := [node84, node85, node86, node87]
theorem entries_count21 : entries21.length = 4 := by decide +kernel
theorem census_node84 : ((verts node84).filter (wye node84)).length = 1 := by decide +kernel
theorem census_node85 : ((verts node85).filter (wye node85)).length = 0 := by decide +kernel
theorem census_node86 : ((verts node86).filter (wye node86)).length = 0 := by decide +kernel
theorem census_node87 : ((verts node87).filter (wye node87)).length = 0 := by decide +kernel
theorem arc_count21 : (entries21.map (fun g => ((verts g).filter (wye g)).length)).sum = 1 := by
  simp only [entries21, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node84, census_node85, census_node86, census_node87]
  decide +kernel
end RawCert
