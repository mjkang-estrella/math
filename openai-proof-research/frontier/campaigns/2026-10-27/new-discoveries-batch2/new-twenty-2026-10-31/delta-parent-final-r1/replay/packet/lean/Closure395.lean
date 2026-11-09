import Closure394
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1580 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower1580 : ∀ h, Pure node1580 h → 11 ≤ h.length := by
  apply indexed_extend node1580 [(3, node829), (8, node808), (10, node793)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower829
  · exact lower808
  · exact lower793
def node1581 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1, 0], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower1581 : ∀ h, Pure node1581 h → 11 ≤ h.length := by
  apply indexed_extend node1581 [(5, node852), (6, node799), (10, node793)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower852
  · exact lower799
  · exact lower793
def node1582 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 0, 1, 1, 0]]
theorem lower1582 : ∀ h, Pure node1582 h → 11 ≤ h.length := by
  apply indexed_extend node1582 [(5, node853), (6, node800), (7, node802), (8, node807), (10, node794)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower853
  · exact lower800
  · exact lower802
  · exact lower807
  · exact lower794
def node1583 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1583 : ∀ h, Pure node1583 h → 11 ≤ h.length := by
  apply indexed_extend node1583 [(3, node830), (7, node803), (8, node809), (10, node795), (11, node794)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower830
  · exact lower803
  · exact lower809
  · exact lower795
  · exact lower794
def entries395 : List Graph := [node1580, node1581, node1582, node1583]
theorem entries_count395 : entries395.length = 4 := by decide +kernel
theorem arc_count395 : (entries395.map (fun g => ((verts g).filter (wye g)).length)).sum = 16 := by decide +kernel
end RawCert
