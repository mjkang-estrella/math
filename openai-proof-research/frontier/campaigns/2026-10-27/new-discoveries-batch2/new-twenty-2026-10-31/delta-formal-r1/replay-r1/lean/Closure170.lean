import Closure169
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node680 : Graph := [[0, 0, 1, 1, 0, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [1, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower680 : ∀ h, Pure node680 h → 11 ≤ h.length := by
  apply indexed_extend node680 [(4, node167), (6, node166), (12, node162)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower167
  · exact lower166
  · exact lower162
def node681 : Graph := [[0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower681 : ∀ h, Pure node681 h → 11 ≤ h.length := by
  apply indexed_extend node681 [(7, node166), (10, node164), (12, node163)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower166
  · exact lower164
  · exact lower163
def node682 : Graph := [[0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1], [1, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower682 : ∀ h, Pure node682 h → 11 ≤ h.length := by
  apply indexed_extend node682 [(7, node167), (10, node165)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower167
  · exact lower165
def node683 : Graph := [[0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower683 : ∀ h, Pure node683 h → 11 ≤ h.length := by
  apply indexed_extend node683 [(4, node168), (6, node169), (7, node170)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower168
  · exact lower169
  · exact lower170
def entries170 : List Graph := [node680, node681, node682, node683]
theorem entries_count170 : entries170.length = 4 := by decide +kernel
theorem arc_count170 : (entries170.map (fun g => ((verts g).filter (wye g)).length)).sum = 11 := by decide +kernel
end RawCert
