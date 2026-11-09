import Closure334
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1340 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0]]
theorem lower1340 : ∀ h, Pure node1340 h → 11 ≤ h.length := by
  apply indexed_extend node1340 [(4, node596), (5, node594), (8, node576), (10, node566), (12, node565)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower596
  · exact lower594
  · exact lower576
  · exact lower566
  · exact lower565
def node1341 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0]]
theorem lower1341 : ∀ h, Pure node1341 h → 11 ≤ h.length := by
  apply indexed_extend node1341 [(5, node595), (6, node620), (10, node566)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower595
  · exact lower620
  · exact lower566
def node1342 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0]]
theorem lower1342 : ∀ h, Pure node1342 h → 11 ≤ h.length := by
  apply indexed_extend node1342 [(4, node597), (6, node621), (7, node573), (10, node567)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower597
  · exact lower621
  · exact lower573
  · exact lower567
def node1343 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0]]
theorem lower1343 : ∀ h, Pure node1343 h → 11 ≤ h.length := by
  apply indexed_extend node1343 [(6, node622), (7, node574), (8, node575), (10, node568)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower622
  · exact lower574
  · exact lower575
  · exact lower568
def entries335 : List Graph := [node1340, node1341, node1342, node1343]
theorem entries_count335 : entries335.length = 4 := by decide +kernel
theorem arc_count335 : (entries335.map (fun g => ((verts g).filter (wye g)).length)).sum = 16 := by decide +kernel
end RawCert
