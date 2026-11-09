import Closure068
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node276 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 2], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0]]
theorem lower276 : ∀ h, Pure node276 h → 11 ≤ h.length := by
  apply indexed_extend node276 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node277 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 2, 0, 0, 1, 1, 0, 0, 1, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1, 1, 1, 2, 0, 0]]
theorem lower277 : ∀ h, Pure node277 h → 11 ≤ h.length := by
  apply indexed_extend node277 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node278 : Graph := [[0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0], [0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3], [1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0]]
theorem lower278 : ∀ h, Pure node278 h → 11 ≤ h.length := by
  apply indexed_extend node278 [(6, node24)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower24
def node279 : Graph := [[0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1], [0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3], [1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 1, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0]]
theorem lower279 : ∀ h, Pure node279 h → 11 ≤ h.length := by
  apply indexed_extend node279 [(5, node24)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower24
def entries69 : List Graph := [node276, node277, node278, node279]
theorem entries_count69 : entries69.length = 4 := by decide +kernel
theorem census_node276 : ((verts node276).filter (wye node276)).length = 0 := by decide +kernel
theorem census_node277 : ((verts node277).filter (wye node277)).length = 0 := by decide +kernel
theorem census_node278 : ((verts node278).filter (wye node278)).length = 1 := by decide +kernel
theorem census_node279 : ((verts node279).filter (wye node279)).length = 1 := by decide +kernel
theorem arc_count69 : (entries69.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by
  simp only [entries69, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node276, census_node277, census_node278, census_node279]
  decide +kernel
end RawCert
