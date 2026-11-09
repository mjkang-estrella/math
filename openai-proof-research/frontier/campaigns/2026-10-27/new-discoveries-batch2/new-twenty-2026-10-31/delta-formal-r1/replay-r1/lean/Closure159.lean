import Closure158
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node636 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0]]
theorem lower636 : ∀ h, Pure node636 h → 11 ≤ h.length := by
  apply indexed_extend node636 [(11, node139)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower139
def node637 : Graph := [[0, 0, 0, 3, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0], [0, 0, 0, 2, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1, 0], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower637 : ∀ h, Pure node637 h → 11 ≤ h.length := by
  apply indexed_extend node637 [(1, node250), (12, node140)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower250
  · exact lower140
def node638 : Graph := [[0, 0, 0, 3, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0]]
theorem lower638 : ∀ h, Pure node638 h → 11 ≤ h.length := by
  apply indexed_extend node638 [(5, node141), (9, node140)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower141
  · exact lower140
def node639 : Graph := [[0, 0, 0, 3, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0], [0, 0, 0, 2, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0]]
theorem lower639 : ∀ h, Pure node639 h → 11 ≤ h.length := by
  apply indexed_extend node639 [(6, node142), (12, node140)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower142
  · exact lower140
def entries159 : List Graph := [node636, node637, node638, node639]
theorem entries_count159 : entries159.length = 4 := by decide +kernel
theorem arc_count159 : (entries159.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by decide +kernel
end RawCert
