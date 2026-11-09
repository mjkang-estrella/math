import Closure354
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1420 : Graph := [[0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0], [0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1420 : ∀ h, Pure node1420 h → 11 ≤ h.length := by
  apply indexed_extend node1420 [(5, node652), (6, node688), (9, node647), (13, node645)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower652
  · exact lower688
  · exact lower647
  · exact lower645
def node1421 : Graph := [[0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1421 : ∀ h, Pure node1421 h → 11 ≤ h.length := by
  apply indexed_extend node1421 [(5, node685), (6, node650), (9, node649), (13, node648)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower685
  · exact lower650
  · exact lower649
  · exact lower648
def node1422 : Graph := [[0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1422 : ∀ h, Pure node1422 h → 11 ≤ h.length := by
  apply indexed_extend node1422 [(5, node686), (7, node652), (9, node651)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower686
  · exact lower652
  · exact lower651
def node1423 : Graph := [[0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1423 : ∀ h, Pure node1423 h → 11 ≤ h.length := by
  apply indexed_extend node1423 [(6, node662), (7, node659), (9, node653)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower662
  · exact lower659
  · exact lower653
def entries355 : List Graph := [node1420, node1421, node1422, node1423]
theorem entries_count355 : entries355.length = 4 := by decide +kernel
theorem arc_count355 : (entries355.map (fun g => ((verts g).filter (wye g)).length)).sum = 14 := by decide +kernel
end RawCert
