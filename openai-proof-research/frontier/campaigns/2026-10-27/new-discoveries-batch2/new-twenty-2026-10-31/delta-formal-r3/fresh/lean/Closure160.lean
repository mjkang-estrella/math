import Closure159
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node640 : Graph := [[0, 0, 0, 3, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower640 : ∀ h, Pure node640 h → 11 ≤ h.length := by
  apply indexed_extend node640 [(1, node251), (12, node141)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower251
  · exact lower141
def node641 : Graph := [[0, 0, 0, 3, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0], [0, 0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0, 0]]
theorem lower641 : ∀ h, Pure node641 h → 11 ≤ h.length := by
  apply indexed_extend node641 [(1, node252), (11, node142)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower252
  · exact lower142
def node642 : Graph := [[0, 0, 0, 3, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0]]
theorem lower642 : ∀ h, Pure node642 h → 11 ≤ h.length := by
  apply indexed_extend node642 [(12, node141)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower141
def node643 : Graph := [[0, 0, 0, 3, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 2, 0]]
theorem lower643 : ∀ h, Pure node643 h → 11 ≤ h.length := by
  apply indexed_extend node643 [(8, node142)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower142
def entries160 : List Graph := [node640, node641, node642, node643]
theorem entries_count160 : entries160.length = 4 := by decide +kernel
theorem census_node640 : ((verts node640).filter (wye node640)).length = 2 := by decide +kernel
theorem census_node641 : ((verts node641).filter (wye node641)).length = 2 := by decide +kernel
theorem census_node642 : ((verts node642).filter (wye node642)).length = 1 := by decide +kernel
theorem census_node643 : ((verts node643).filter (wye node643)).length = 1 := by decide +kernel
theorem arc_count160 : (entries160.map (fun g => ((verts g).filter (wye g)).length)).sum = 6 := by
  simp only [entries160, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node640, census_node641, census_node642, census_node643]
  decide +kernel
end RawCert
