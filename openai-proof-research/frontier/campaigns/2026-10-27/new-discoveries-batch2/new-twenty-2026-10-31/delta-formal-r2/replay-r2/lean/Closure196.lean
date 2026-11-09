import Closure195
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node784 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1, 0], [1, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower784 : ∀ h, Pure node784 h → 11 ≤ h.length := by
  apply indexed_extend node784 [(8, node199), (10, node197)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower199
  · exact lower197
def node785 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower785 : ∀ h, Pure node785 h → 11 ≤ h.length := by
  apply indexed_extend node785 [(4, node204), (8, node199), (12, node196)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower204
  · exact lower199
  · exact lower196
def node786 : Graph := [[0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 0, 1, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower786 : ∀ h, Pure node786 h → 11 ≤ h.length := by
  apply indexed_extend node786 [(7, node204), (10, node201), (12, node200)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower204
  · exact lower201
  · exact lower200
def node787 : Graph := [[0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [1, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower787 : ∀ h, Pure node787 h → 11 ≤ h.length := by
  apply indexed_extend node787 [(8, node205), (10, node203), (12, node202)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower205
  · exact lower203
  · exact lower202
def entries196 : List Graph := [node784, node785, node786, node787]
theorem entries_count196 : entries196.length = 4 := by decide +kernel
theorem arc_count196 : (entries196.map (fun g => ((verts g).filter (wye g)).length)).sum = 11 := by decide +kernel
end RawCert
