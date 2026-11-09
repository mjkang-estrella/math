import Closure071
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node288 : Graph := [[0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower288 : ∀ h, Pure node288 h → 11 ≤ h.length := by
  apply indexed_extend node288 [(4, node33), (12, node25)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower33
  · exact lower25
def node289 : Graph := [[0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [0, 1, 2, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0], [0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower289 : ∀ h, Pure node289 h → 11 ≤ h.length := by
  apply indexed_extend node289 [(5, node34), (12, node26)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower34
  · exact lower26
def node290 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3], [0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower290 : ∀ h, Pure node290 h → 11 ≤ h.length := by
  apply indexed_extend node290 [(2, node37), (6, node28), (8, node27)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower37
  · exact lower28
  · exact lower27
def node291 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3], [0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower291 : ∀ h, Pure node291 h → 11 ≤ h.length := by
  apply indexed_extend node291 [(3, node37), (6, node29), (7, node30)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower37
  · exact lower29
  · exact lower30
def entries72 : List Graph := [node288, node289, node290, node291]
theorem entries_count72 : entries72.length = 4 := by decide +kernel
theorem arc_count72 : (entries72.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by decide +kernel
end RawCert
