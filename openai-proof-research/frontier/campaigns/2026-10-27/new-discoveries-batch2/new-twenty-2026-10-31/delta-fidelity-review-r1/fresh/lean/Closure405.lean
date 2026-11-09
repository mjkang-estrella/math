import Closure404
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1620 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 1, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower1620 : ∀ h, Pure node1620 h → 11 ≤ h.length := by
  apply indexed_extend node1620 [(5, node839), (7, node843), (9, node829)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower839
  · exact lower843
  · exact lower829
def node1621 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1621 : ∀ h, Pure node1621 h → 11 ≤ h.length := by
  apply indexed_extend node1621 [(5, node840), (6, node841), (7, node844), (9, node830)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower840
  · exact lower841
  · exact lower844
  · exact lower830
def node1622 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower1622 : ∀ h, Pure node1622 h → 11 ≤ h.length := by
  apply indexed_extend node1622 [(6, node842), (7, node845), (10, node830), (13, node829)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower842
  · exact lower845
  · exact lower830
  · exact lower829
def node1623 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 1, 0], [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0]]
theorem lower1623 : ∀ h, Pure node1623 h → 11 ≤ h.length := by
  apply indexed_extend node1623 [(3, node882), (5, node846), (9, node831)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower882
  · exact lower846
  · exact lower831
def entries405 : List Graph := [node1620, node1621, node1622, node1623]
theorem entries_count405 : entries405.length = 4 := by decide +kernel
theorem arc_count405 : (entries405.map (fun g => ((verts g).filter (wye g)).length)).sum = 14 := by decide +kernel
end RawCert
