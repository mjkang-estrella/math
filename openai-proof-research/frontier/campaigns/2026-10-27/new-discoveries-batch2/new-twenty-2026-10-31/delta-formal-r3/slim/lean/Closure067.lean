import Closure066
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node268 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1], [0, 0, 2, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 3, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0]]
theorem lower268 : ∀ h, Pure node268 h → 11 ≤ h.length := by
  apply indexed_extend node268 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node269 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3], [1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0]]
theorem lower269 : ∀ h, Pure node269 h → 11 ≤ h.length := by
  apply indexed_extend node269 [(3, node23), (6, node24)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower23
  · exact lower24
def node270 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [0, 0, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 2], [2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower270 : ∀ h, Pure node270 h → 11 ≤ h.length := by
  apply indexed_extend node270 [(11, node22)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower22
def node271 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [0, 0, 1, 2, 0, 1, 0, 1, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1], [2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 2, 0]]
theorem lower271 : ∀ h, Pure node271 h → 11 ≤ h.length := by
  apply indexed_extend node271 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries67 : List Graph := [node268, node269, node270, node271]
theorem entries_count67 : entries67.length = 4 := by decide +kernel
theorem census_node268 : ((verts node268).filter (wye node268)).length = 0 := by decide +kernel
theorem census_node269 : ((verts node269).filter (wye node269)).length = 2 := by decide +kernel
theorem census_node270 : ((verts node270).filter (wye node270)).length = 1 := by decide +kernel
theorem census_node271 : ((verts node271).filter (wye node271)).length = 0 := by decide +kernel
theorem arc_count67 : (entries67.map (fun g => ((verts g).filter (wye g)).length)).sum = 3 := by
  simp only [entries67, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node268, census_node269, census_node270, census_node271]
  decide +kernel
end RawCert
