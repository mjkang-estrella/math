import Closure019
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node80 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2], [0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0]]
theorem lower80 : ∀ h, Pure node80 h → 11 ≤ h.length := by
  apply indexed_extend node80 [(8, node4)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower4
def node81 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 1, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [0, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 1, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 3, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower81 : ∀ h, Pure node81 h → 11 ≤ h.length := by
  apply indexed_extend node81 [(2, node13), (9, node4)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower13
  · exact lower4
def node82 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [0, 1, 2, 0, 0, 1, 1, 0, 0, 1, 0, 0], [0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 1, 1, 2, 0, 0, 0]]
theorem lower82 : ∀ h, Pure node82 h → 11 ≤ h.length := by
  apply indexed_extend node82 [(8, node5)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower5
def node83 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [0, 1, 2, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [1, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower83 : ∀ h, Pure node83 h → 11 ≤ h.length := by
  apply indexed_extend node83 [(2, node14), (9, node5)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower14
  · exact lower5
def entries20 : List Graph := [node80, node81, node82, node83]
theorem entries_count20 : entries20.length = 4 := by decide +kernel
theorem census_node80 : ((verts node80).filter (wye node80)).length = 1 := by decide +kernel
theorem census_node81 : ((verts node81).filter (wye node81)).length = 2 := by decide +kernel
theorem census_node82 : ((verts node82).filter (wye node82)).length = 1 := by decide +kernel
theorem census_node83 : ((verts node83).filter (wye node83)).length = 2 := by decide +kernel
theorem arc_count20 : (entries20.map (fun g => ((verts g).filter (wye g)).length)).sum = 6 := by
  simp only [entries20, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node80, census_node81, census_node82, census_node83]
  decide +kernel
end RawCert
