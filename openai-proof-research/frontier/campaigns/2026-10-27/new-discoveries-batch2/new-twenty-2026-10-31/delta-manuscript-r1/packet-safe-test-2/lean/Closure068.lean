import Closure067
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node272 : Graph := [[0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 1], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3], [1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1], [0, 0, 3, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0]]
theorem lower272 : ∀ h, Pure node272 h → 11 ≤ h.length := by
  apply indexed_extend node272 [(6, node23)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower23
def node273 : Graph := [[0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 2], [2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 3, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower273 : ∀ h, Pure node273 h → 11 ≤ h.length := by
  apply indexed_extend node273 [(11, node23)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower23
def node274 : Graph := [[0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0], [0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 3, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower274 : ∀ h, Pure node274 h → 11 ≤ h.length := by
  apply indexed_extend node274 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node275 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2], [1, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0]]
theorem lower275 : ∀ h, Pure node275 h → 11 ≤ h.length := by
  apply indexed_extend node275 [(3, node24)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower24
def entries68 : List Graph := [node272, node273, node274, node275]
theorem entries_count68 : entries68.length = 4 := by decide +kernel
theorem census_node272 : ((verts node272).filter (wye node272)).length = 1 := by decide +kernel
theorem census_node273 : ((verts node273).filter (wye node273)).length = 1 := by decide +kernel
theorem census_node274 : ((verts node274).filter (wye node274)).length = 0 := by decide +kernel
theorem census_node275 : ((verts node275).filter (wye node275)).length = 1 := by decide +kernel
theorem arc_count68 : (entries68.map (fun g => ((verts g).filter (wye g)).length)).sum = 3 := by
  simp only [entries68, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node272, census_node273, census_node274, census_node275]
  decide +kernel
end RawCert
