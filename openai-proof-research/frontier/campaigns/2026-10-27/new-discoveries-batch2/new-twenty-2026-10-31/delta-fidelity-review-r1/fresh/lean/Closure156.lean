import Closure155
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node624 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower624 : ∀ h, Pure node624 h → 11 ≤ h.length := by
  apply indexed_extend node624 [(1, node241), (11, node133)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower241
  · exact lower133
def node625 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 2, 0, 0]]
theorem lower625 : ∀ h, Pure node625 h → 11 ≤ h.length := by
  apply indexed_extend node625 [(1, node242), (11, node134)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower242
  · exact lower134
def node626 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower626 : ∀ h, Pure node626 h → 11 ≤ h.length := by
  apply indexed_extend node626 [(1, node243), (11, node135), (12, node129)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower243
  · exact lower135
  · exact lower129
def node627 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [1, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0, 0]]
theorem lower627 : ∀ h, Pure node627 h → 11 ≤ h.length := by
  apply indexed_extend node627 [(1, node244), (11, node136)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower244
  · exact lower136
def entries156 : List Graph := [node624, node625, node626, node627]
theorem entries_count156 : entries156.length = 4 := by decide +kernel
theorem arc_count156 : (entries156.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by decide +kernel
end RawCert
