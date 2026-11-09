import Closure178
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node716 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0]]
theorem lower716 : ∀ h, Pure node716 h → 11 ≤ h.length := by
  apply indexed_extend node716 [(0, node88), (2, node55), (9, node211)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower88
  · exact lower55
  · exact lower211
def node717 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower717 : ∀ h, Pure node717 h → 11 ≤ h.length := by
  apply indexed_extend node717 [(0, node25), (2, node93), (4, node189), (5, node182)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower25
  · exact lower93
  · exact lower189
  · exact lower182
def node718 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 0], [0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower718 : ∀ h, Pure node718 h → 11 ≤ h.length := by
  apply indexed_extend node718 [(0, node26), (2, node94), (10, node216)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower26
  · exact lower94
  · exact lower216
def node719 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 0, 1, 0], [0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower719 : ∀ h, Pure node719 h → 11 ≤ h.length := by
  apply indexed_extend node719 [(0, node27), (4, node190), (7, node182), (10, node217)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower27
  · exact lower190
  · exact lower182
  · exact lower217
def entries179 : List Graph := [node716, node717, node718, node719]
theorem entries_count179 : entries179.length = 4 := by decide +kernel
theorem census_node716 : ((verts node716).filter (wye node716)).length = 3 := by decide +kernel
theorem census_node717 : ((verts node717).filter (wye node717)).length = 4 := by decide +kernel
theorem census_node718 : ((verts node718).filter (wye node718)).length = 3 := by decide +kernel
theorem census_node719 : ((verts node719).filter (wye node719)).length = 4 := by decide +kernel
theorem arc_count179 : (entries179.map (fun g => ((verts g).filter (wye g)).length)).sum = 14 := by
  simp only [entries179, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node716, census_node717, census_node718, census_node719]
  decide +kernel
end RawCert
