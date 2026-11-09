import Closure024
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node100 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 0, 2, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0]]
theorem lower100 : ∀ h, Pure node100 h → 11 ≤ h.length := by
  apply indexed_extend node100 [(5, node6)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower6
def node101 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3], [0, 0, 0, 1, 0, 0, 0, 2, 1, 1, 0, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 1, 1, 0, 0, 1, 0, 0]]
theorem lower101 : ∀ h, Pure node101 h → 11 ≤ h.length := by
  apply indexed_extend node101 [(7, node6), (10, node8)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower6
  · exact lower8
def node102 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 2, 0, 2, 0, 0]]
theorem lower102 : ∀ h, Pure node102 h → 11 ≤ h.length := by
  apply indexed_extend node102 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node103 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [2, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 1], [0, 2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower103 : ∀ h, Pure node103 h → 11 ≤ h.length := by
  apply indexed_extend node103 [(5, node7)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower7
def entries25 : List Graph := [node100, node101, node102, node103]
theorem entries_count25 : entries25.length = 4 := by decide +kernel
theorem arc_count25 : (entries25.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by decide +kernel
end RawCert
