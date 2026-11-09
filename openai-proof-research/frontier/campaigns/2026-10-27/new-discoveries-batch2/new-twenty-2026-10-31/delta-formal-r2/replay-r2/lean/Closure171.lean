import Closure170
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node684 : Graph := [[0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower684 : ∀ h, Pure node684 h → 11 ≤ h.length := by
  apply indexed_extend node684 [(4, node171), (5, node172), (6, node173), (7, node174)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower171
  · exact lower172
  · exact lower173
  · exact lower174
def node685 : Graph := [[0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower685 : ∀ h, Pure node685 h → 11 ≤ h.length := by
  apply indexed_extend node685 [(5, node175), (8, node171), (12, node168)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower175
  · exact lower171
  · exact lower168
def node686 : Graph := [[0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 1], [0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower686 : ∀ h, Pure node686 h → 11 ≤ h.length := by
  apply indexed_extend node686 [(6, node176), (8, node172)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower176
  · exact lower172
def node687 : Graph := [[0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 2], [0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower687 : ∀ h, Pure node687 h → 11 ≤ h.length := by
  apply indexed_extend node687 [(4, node175), (8, node173), (12, node169)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower175
  · exact lower173
  · exact lower169
def entries171 : List Graph := [node684, node685, node686, node687]
theorem entries_count171 : entries171.length = 4 := by decide +kernel
theorem arc_count171 : (entries171.map (fun g => ((verts g).filter (wye g)).length)).sum = 12 := by decide +kernel
end RawCert
