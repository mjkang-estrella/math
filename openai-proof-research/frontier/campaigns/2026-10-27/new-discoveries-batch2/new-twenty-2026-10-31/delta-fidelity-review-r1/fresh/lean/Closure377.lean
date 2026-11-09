import Closure376
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1508 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1508 : ∀ h, Pure node1508 h → 11 ≤ h.length := by
  apply indexed_extend node1508 [(0, node693), (3, node790), (7, node727), (11, node846)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower693
  · exact lower790
  · exact lower727
  · exact lower846
def node1509 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1509 : ∀ h, Pure node1509 h → 11 ≤ h.length := by
  apply indexed_extend node1509 [(0, node288), (2, node505), (4, node776), (5, node728), (13, node717)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower288
  · exact lower505
  · exact lower776
  · exact lower728
  · exact lower717
def node1510 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1510 : ∀ h, Pure node1510 h → 11 ≤ h.length := by
  apply indexed_extend node1510 [(0, node289), (2, node506), (6, node729), (10, node828), (13, node718)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower289
  · exact lower506
  · exact lower729
  · exact lower828
  · exact lower718
def node1511 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1511 : ∀ h, Pure node1511 h → 11 ≤ h.length := by
  apply indexed_extend node1511 [(0, node294), (4, node777), (7, node728), (10, node836), (13, node719)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower294
  · exact lower777
  · exact lower728
  · exact lower836
  · exact lower719
def entries377 : List Graph := [node1508, node1509, node1510, node1511]
theorem entries_count377 : entries377.length = 4 := by decide +kernel
theorem arc_count377 : (entries377.map (fun g => ((verts g).filter (wye g)).length)).sum = 19 := by decide +kernel
end RawCert
