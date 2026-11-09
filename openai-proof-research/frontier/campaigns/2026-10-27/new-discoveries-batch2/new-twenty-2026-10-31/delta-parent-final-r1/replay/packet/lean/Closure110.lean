import Closure109
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node440 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [0, 1, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower440 : ∀ h, Pure node440 h → 11 ≤ h.length := by
  apply indexed_extend node440 [(2, node174), (6, node83), (10, node78)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower174
  · exact lower83
  · exact lower78
def node441 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower441 : ∀ h, Pure node441 h → 11 ≤ h.length := by
  apply indexed_extend node441 [(3, node25), (5, node84)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower25
  · exact lower84
def node442 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0], [0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 0], [1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower442 : ∀ h, Pure node442 h → 11 ≤ h.length := by
  apply indexed_extend node442 [(3, node26)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower26
def node443 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower443 : ∀ h, Pure node443 h → 11 ≤ h.length := by
  apply indexed_extend node443 [(2, node175), (8, node81), (10, node80), (12, node79)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower175
  · exact lower81
  · exact lower80
  · exact lower79
def entries110 : List Graph := [node440, node441, node442, node443]
theorem entries_count110 : entries110.length = 4 := by decide +kernel
theorem arc_count110 : (entries110.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by decide +kernel
end RawCert
