import Closure149
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node600 : Graph := [[0, 0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower600 : ∀ h, Pure node600 h → 11 ≤ h.length := by
  apply indexed_extend node600 [(2, node225)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower225
def node601 : Graph := [[0, 0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower601 : ∀ h, Pure node601 h → 11 ≤ h.length := by
  apply indexed_extend node601 [(2, node226), (8, node124)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower226
  · exact lower124
def node602 : Graph := [[0, 0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 2, 0, 0]]
theorem lower602 : ∀ h, Pure node602 h → 11 ≤ h.length := by
  apply indexed_extend node602 [(2, node227), (9, node124), (11, node126)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower227
  · exact lower124
  · exact lower126
def node603 : Graph := [[0, 0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0]]
theorem lower603 : ∀ h, Pure node603 h → 11 ≤ h.length := by
  apply indexed_extend node603 [(12, node125)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower125
def entries150 : List Graph := [node600, node601, node602, node603]
theorem entries_count150 : entries150.length = 4 := by decide +kernel
theorem arc_count150 : (entries150.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by decide +kernel
end RawCert
