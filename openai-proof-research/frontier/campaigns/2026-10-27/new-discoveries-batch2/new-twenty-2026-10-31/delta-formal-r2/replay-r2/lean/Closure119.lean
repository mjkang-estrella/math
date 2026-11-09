import Closure118
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node476 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1], [0, 0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0]]
theorem lower476 : ∀ h, Pure node476 h → 11 ≤ h.length := by
  apply indexed_extend node476 [(0, node280), (3, node44), (11, node123)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower280
  · exact lower44
  · exact lower123
def node477 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower477 : ∀ h, Pure node477 h → 11 ≤ h.length := by
  apply indexed_extend node477 [(0, node253), (1, node182), (5, node113), (12, node89)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower253
  · exact lower182
  · exact lower113
  · exact lower89
def node478 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 3, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower478 : ∀ h, Pure node478 h → 11 ≤ h.length := by
  apply indexed_extend node478 [(0, node257), (2, node183), (12, node90)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower257
  · exact lower183
  · exact lower90
def node479 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower479 : ∀ h, Pure node479 h → 11 ≤ h.length := by
  apply indexed_extend node479 [(0, node270), (5, node115), (12, node89)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower270
  · exact lower115
  · exact lower89
def entries119 : List Graph := [node476, node477, node478, node479]
theorem entries_count119 : entries119.length = 4 := by decide +kernel
theorem arc_count119 : (entries119.map (fun g => ((verts g).filter (wye g)).length)).sum = 13 := by decide +kernel
end RawCert
