import Closure435
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1744 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 2, 0]]
theorem lower1744 : ∀ h, Pure node1744 h → 11 ≤ h.length := by
  apply indexed_extend node1744 [(3, node968), (8, node965), (12, node961)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower968
  · exact lower965
  · exact lower961
def node1745 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower1745 : ∀ h, Pure node1745 h → 11 ≤ h.length := by
  apply indexed_extend node1745 [(3, node969), (6, node964), (12, node962), (13, node959)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower969
  · exact lower964
  · exact lower962
  · exact lower959
def node1746 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower1746 : ∀ h, Pure node1746 h → 11 ≤ h.length := by
  apply indexed_extend node1746 [(3, node970), (7, node965), (12, node963), (13, node960)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower970
  · exact lower965
  · exact lower963
  · exact lower960
def node1747 : Graph := [[0, 3, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0], [1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1747 : ∀ h, Pure node1747 h → 11 ≤ h.length := by
  apply indexed_extend node1747 [(5, node967), (6, node968), (7, node969), (8, node970), (13, node966)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower967
  · exact lower968
  · exact lower969
  · exact lower970
  · exact lower966
def entries436 : List Graph := [node1744, node1745, node1746, node1747]
theorem entries_count436 : entries436.length = 4 := by decide +kernel
theorem arc_count436 : (entries436.map (fun g => ((verts g).filter (wye g)).length)).sum = 16 := by decide +kernel
end RawCert
