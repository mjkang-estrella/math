import Closure428
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1716 : Graph := [[0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower1716 : ∀ h, Pure node1716 h → 11 ≤ h.length := by
  apply indexed_extend node1716 [(4, node929), (6, node934), (8, node962)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower929
  · exact lower934
  · exact lower962
def node1717 : Graph := [[0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower1717 : ∀ h, Pure node1717 h → 11 ≤ h.length := by
  apply indexed_extend node1717 [(4, node930), (7, node935), (8, node963)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower930
  · exact lower935
  · exact lower963
def node1718 : Graph := [[0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0]]
theorem lower1718 : ∀ h, Pure node1718 h → 11 ≤ h.length := by
  apply indexed_extend node1718 [(4, node931), (6, node932), (9, node925), (10, node926)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower931
  · exact lower932
  · exact lower925
  · exact lower926
def node1719 : Graph := [[0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower1719 : ∀ h, Pure node1719 h → 11 ≤ h.length := by
  apply indexed_extend node1719 [(4, node938), (6, node940), (13, node925)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower938
  · exact lower940
  · exact lower925
def entries429 : List Graph := [node1716, node1717, node1718, node1719]
theorem entries_count429 : entries429.length = 4 := by decide +kernel
theorem arc_count429 : (entries429.map (fun g => ((verts g).filter (wye g)).length)).sum = 13 := by decide +kernel
end RawCert
