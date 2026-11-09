import Closure136
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node548 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 0], [1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower548 : ∀ h, Pure node548 h → 11 ≤ h.length := by
  apply indexed_extend node548 [(2, node202), (12, node111)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower202
  · exact lower111
def node549 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 2], [1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 1, 2, 0, 0, 0]]
theorem lower549 : ∀ h, Pure node549 h → 11 ≤ h.length := by
  apply indexed_extend node549 [(2, node203), (9, node114), (11, node112)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower203
  · exact lower114
  · exact lower112
def node550 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower550 : ∀ h, Pure node550 h → 11 ≤ h.length := by
  apply indexed_extend node550 [(8, node115), (11, node110), (12, node109)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower115
  · exact lower110
  · exact lower109
def node551 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 2], [1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower551 : ∀ h, Pure node551 h → 11 ≤ h.length := by
  apply indexed_extend node551 [(11, node112), (12, node111)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower112
  · exact lower111
def entries137 : List Graph := [node548, node549, node550, node551]
theorem entries_count137 : entries137.length = 4 := by decide +kernel
theorem arc_count137 : (entries137.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by decide +kernel
end RawCert
