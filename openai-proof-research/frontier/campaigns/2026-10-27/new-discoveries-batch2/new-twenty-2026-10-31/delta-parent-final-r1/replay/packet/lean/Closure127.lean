import Closure126
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node508 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower508 : ∀ h, Pure node508 h → 11 ≤ h.length := by
  apply indexed_extend node508 [(3, node167), (7, node102)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower167
  · exact lower102
def node509 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower509 : ∀ h, Pure node509 h → 11 ≤ h.length := by
  apply indexed_extend node509 [(6, node105)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower105
def node510 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [2, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0], [1, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower510 : ∀ h, Pure node510 h → 11 ≤ h.length := by
  apply indexed_extend node510 [(5, node103), (6, node106)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower103
  · exact lower106
def node511 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower511 : ∀ h, Pure node511 h → 11 ≤ h.length := by
  apply indexed_extend node511 [(5, node104), (7, node103)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower104
  · exact lower103
def entries127 : List Graph := [node508, node509, node510, node511]
theorem entries_count127 : entries127.length = 4 := by decide +kernel
theorem arc_count127 : (entries127.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by decide +kernel
end RawCert
