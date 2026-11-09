import Closure358
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1436 : Graph := [[0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1436 : ∀ h, Pure node1436 h → 11 ≤ h.length := by
  apply indexed_extend node1436 [(4, node682), (6, node681), (8, node680), (11, node679), (13, node678)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower682
  · exact lower681
  · exact lower680
  · exact lower679
  · exact lower678
def node1437 : Graph := [[0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1437 : ∀ h, Pure node1437 h → 11 ≤ h.length := by
  apply indexed_extend node1437 [(4, node685), (5, node686), (6, node687), (7, node688), (9, node684), (13, node683)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower685
  · exact lower686
  · exact lower687
  · exact lower688
  · exact lower684
  · exact lower683
def node1438 : Graph := [[0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [1, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1438 : ∀ h, Pure node1438 h → 11 ≤ h.length := by
  apply indexed_extend node1438 [(2, node291), (4, node693), (7, node689), (8, node690)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower291
  · exact lower693
  · exact lower689
  · exact lower690
def node1439 : Graph := [[0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [1, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1439 : ∀ h, Pure node1439 h → 11 ≤ h.length := by
  apply indexed_extend node1439 [(4, node694), (5, node696), (7, node691), (8, node692)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower694
  · exact lower696
  · exact lower691
  · exact lower692
def entries359 : List Graph := [node1436, node1437, node1438, node1439]
theorem entries_count359 : entries359.length = 4 := by decide +kernel
theorem arc_count359 : (entries359.map (fun g => ((verts g).filter (wye g)).length)).sum = 19 := by decide +kernel
end RawCert
