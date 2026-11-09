import Closure414
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1660 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1660 : ∀ h, Pure node1660 h → 11 ≤ h.length := by
  apply indexed_extend node1660 [(0, node690), (1, node645), (3, node896), (7, node918), (13, node937)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower690
  · exact lower645
  · exact lower896
  · exact lower918
  · exact lower937
def node1661 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower1661 : ∀ h, Pure node1661 h → 11 ≤ h.length := by
  apply indexed_extend node1661 [(0, node286), (5, node898), (12, node929)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower286
  · exact lower898
  · exact lower929
def node1662 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [0, 0, 1, 2, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower1662 : ∀ h, Pure node1662 h → 11 ≤ h.length := by
  apply indexed_extend node1662 [(0, node287), (6, node899), (12, node930)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower287
  · exact lower899
  · exact lower930
def node1663 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1663 : ∀ h, Pure node1663 h → 11 ≤ h.length := by
  apply indexed_extend node1663 [(0, node288), (5, node900), (12, node938), (13, node886)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower288
  · exact lower900
  · exact lower938
  · exact lower886
def entries415 : List Graph := [node1660, node1661, node1662, node1663]
theorem entries_count415 : entries415.length = 4 := by decide +kernel
theorem arc_count415 : (entries415.map (fun g => ((verts g).filter (wye g)).length)).sum = 15 := by decide +kernel
end RawCert
