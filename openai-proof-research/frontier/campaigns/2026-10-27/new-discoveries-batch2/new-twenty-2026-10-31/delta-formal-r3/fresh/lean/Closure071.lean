import Closure070
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node284 : Graph := [[0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower284 : ∀ h, Pure node284 h → 11 ≤ h.length := by
  apply indexed_extend node284 [(2, node30), (8, node26)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower30
  · exact lower26
def node285 : Graph := [[0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower285 : ∀ h, Pure node285 h → 11 ≤ h.length := by
  apply indexed_extend node285 [(4, node27), (7, node25), (8, node26)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower27
  · exact lower25
  · exact lower26
def node286 : Graph := [[0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower286 : ∀ h, Pure node286 h → 11 ≤ h.length := by
  apply indexed_extend node286 [(4, node31)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower31
def node287 : Graph := [[0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 2, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower287 : ∀ h, Pure node287 h → 11 ≤ h.length := by
  apply indexed_extend node287 [(5, node32)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower32
def entries71 : List Graph := [node284, node285, node286, node287]
theorem entries_count71 : entries71.length = 4 := by decide +kernel
theorem census_node284 : ((verts node284).filter (wye node284)).length = 2 := by decide +kernel
theorem census_node285 : ((verts node285).filter (wye node285)).length = 3 := by decide +kernel
theorem census_node286 : ((verts node286).filter (wye node286)).length = 1 := by decide +kernel
theorem census_node287 : ((verts node287).filter (wye node287)).length = 1 := by decide +kernel
theorem arc_count71 : (entries71.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by
  simp only [entries71, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node284, census_node285, census_node286, census_node287]
  decide +kernel
end RawCert
