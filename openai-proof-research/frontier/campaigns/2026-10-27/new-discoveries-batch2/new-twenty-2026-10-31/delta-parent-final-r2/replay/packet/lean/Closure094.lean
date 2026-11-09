import Closure093
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node376 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 2], [0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower376 : ∀ h, Pure node376 h → 11 ≤ h.length := by
  apply indexed_extend node376 [(2, node105)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower105
def node377 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0], [1, 0, 0, 0, 1, 0, 2, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower377 : ∀ h, Pure node377 h → 11 ≤ h.length := by
  apply indexed_extend node377 [(2, node106), (6, node56)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower106
  · exact lower56
def node378 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0, 0]]
theorem lower378 : ∀ h, Pure node378 h → 11 ≤ h.length := by
  apply indexed_extend node378 [(2, node107), (8, node56), (11, node52)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower107
  · exact lower56
  · exact lower52
def node379 : Graph := [[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower379 : ∀ h, Pure node379 h → 11 ≤ h.length := by
  apply indexed_extend node379 [(5, node57)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower57
def entries94 : List Graph := [node376, node377, node378, node379]
theorem entries_count94 : entries94.length = 4 := by decide +kernel
theorem census_node376 : ((verts node376).filter (wye node376)).length = 1 := by decide +kernel
theorem census_node377 : ((verts node377).filter (wye node377)).length = 2 := by decide +kernel
theorem census_node378 : ((verts node378).filter (wye node378)).length = 3 := by decide +kernel
theorem census_node379 : ((verts node379).filter (wye node379)).length = 1 := by decide +kernel
theorem arc_count94 : (entries94.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by
  simp only [entries94, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node376, census_node377, census_node378, census_node379]
  decide +kernel
end RawCert
