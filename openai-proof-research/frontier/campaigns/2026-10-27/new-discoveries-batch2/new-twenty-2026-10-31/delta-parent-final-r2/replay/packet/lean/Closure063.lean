import Closure062
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node252 : Graph := [[0, 0, 3, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0], [0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0, 0]]
theorem lower252 : ∀ h, Pure node252 h → 11 ≤ h.length := by
  apply indexed_extend node252 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node253 : Graph := [[0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [0, 0, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0], [2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower253 : ∀ h, Pure node253 h → 11 ≤ h.length := by
  apply indexed_extend node253 [(0, node0), (11, node22)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower0
  · exact lower22
def node254 : Graph := [[0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2], [0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 0], [2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 0, 3, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower254 : ∀ h, Pure node254 h → 11 ≤ h.length := by
  apply indexed_extend node254 [(0, node1), (11, node23)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower1
  · exact lower23
def node255 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 1, 1, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 2], [0, 0, 1, 0, 0, 2, 2, 0, 0, 1, 0, 0], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 1, 1, 0, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0]]
theorem lower255 : ∀ h, Pure node255 h → 11 ≤ h.length := by
  apply indexed_extend node255 [(1, node4)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower4
def entries63 : List Graph := [node252, node253, node254, node255]
theorem entries_count63 : entries63.length = 4 := by decide +kernel
theorem census_node252 : ((verts node252).filter (wye node252)).length = 0 := by decide +kernel
theorem census_node253 : ((verts node253).filter (wye node253)).length = 2 := by decide +kernel
theorem census_node254 : ((verts node254).filter (wye node254)).length = 2 := by decide +kernel
theorem census_node255 : ((verts node255).filter (wye node255)).length = 1 := by decide +kernel
theorem arc_count63 : (entries63.map (fun g => ((verts g).filter (wye g)).length)).sum = 5 := by
  simp only [entries63, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node252, census_node253, census_node254, census_node255]
  decide +kernel
end RawCert
