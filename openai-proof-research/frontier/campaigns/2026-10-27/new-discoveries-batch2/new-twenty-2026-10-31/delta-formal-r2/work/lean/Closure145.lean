import Closure144
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node580 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0]]
theorem lower580 : ∀ h, Pure node580 h → 11 ≤ h.length := by
  apply indexed_extend node580 [(5, node127), (6, node120), (10, node119)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower127
  · exact lower120
  · exact lower119
def node581 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0]]
theorem lower581 : ∀ h, Pure node581 h → 11 ≤ h.length := by
  apply indexed_extend node581 [(4, node140), (8, node123)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower140
  · exact lower123
def node582 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0]]
theorem lower582 : ∀ h, Pure node582 h → 11 ≤ h.length := by
  apply indexed_extend node582 [(7, node122), (12, node119)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower122
  · exact lower119
def node583 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower583 : ∀ h, Pure node583 h → 11 ≤ h.length := by
  apply indexed_extend node583 [(1, node217), (5, node129), (12, node120)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower217
  · exact lower129
  · exact lower120
def entries145 : List Graph := [node580, node581, node582, node583]
theorem entries_count145 : entries145.length = 4 := by decide +kernel
theorem arc_count145 : (entries145.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by decide +kernel
end RawCert
