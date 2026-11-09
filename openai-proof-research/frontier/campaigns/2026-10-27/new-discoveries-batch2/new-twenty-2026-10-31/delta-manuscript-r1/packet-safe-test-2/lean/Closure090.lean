import Closure089
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node360 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower360 : ∀ h, Pure node360 h → 11 ≤ h.length := by
  apply indexed_extend node360 [(6, node53)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower53
def node361 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower361 : ∀ h, Pure node361 h → 11 ≤ h.length := by
  apply indexed_extend node361 [(2, node103), (6, node54), (8, node53), (10, node45)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower103
  · exact lower54
  · exact lower53
  · exact lower45
def node362 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 1], [0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower362 : ∀ h, Pure node362 h → 11 ≤ h.length := by
  apply indexed_extend node362 [(4, node154), (8, node53)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower154
  · exact lower53
def node363 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 1], [0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 2, 0, 0]]
theorem lower363 : ∀ h, Pure node363 h → 11 ≤ h.length := by
  apply indexed_extend node363 [(8, node53)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower53
def entries90 : List Graph := [node360, node361, node362, node363]
theorem entries_count90 : entries90.length = 4 := by decide +kernel
theorem census_node360 : ((verts node360).filter (wye node360)).length = 1 := by decide +kernel
theorem census_node361 : ((verts node361).filter (wye node361)).length = 4 := by decide +kernel
theorem census_node362 : ((verts node362).filter (wye node362)).length = 2 := by decide +kernel
theorem census_node363 : ((verts node363).filter (wye node363)).length = 1 := by decide +kernel
theorem arc_count90 : (entries90.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by
  simp only [entries90, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node360, census_node361, census_node362, census_node363]
  decide +kernel
end RawCert
