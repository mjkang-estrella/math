import Closure041
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node168 : Graph := [[0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3], [0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower168 : ∀ h, Pure node168 h → 11 ≤ h.length := by
  apply indexed_extend node168 [(5, node12)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower12
def node169 : Graph := [[0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower169 : ∀ h, Pure node169 h → 11 ≤ h.length := by
  apply indexed_extend node169 [(4, node12)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower12
def node170 : Graph := [[0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0], [0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower170 : ∀ h, Pure node170 h → 11 ≤ h.length := by
  apply indexed_extend node170 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node171 : Graph := [[0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0], [0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower171 : ∀ h, Pure node171 h → 11 ≤ h.length := by
  apply indexed_extend node171 [(5, node13)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower13
def entries42 : List Graph := [node168, node169, node170, node171]
theorem entries_count42 : entries42.length = 4 := by decide +kernel
theorem census_node168 : ((verts node168).filter (wye node168)).length = 1 := by decide +kernel
theorem census_node169 : ((verts node169).filter (wye node169)).length = 1 := by decide +kernel
theorem census_node170 : ((verts node170).filter (wye node170)).length = 0 := by decide +kernel
theorem census_node171 : ((verts node171).filter (wye node171)).length = 1 := by decide +kernel
theorem arc_count42 : (entries42.map (fun g => ((verts g).filter (wye g)).length)).sum = 3 := by
  simp only [entries42, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node168, census_node169, census_node170, census_node171]
  decide +kernel
end RawCert
