import Closure127
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node512 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [2, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1], [0, 2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower512 : ∀ h, Pure node512 h → 11 ≤ h.length := by
  apply indexed_extend node512 [(5, node107), (8, node103)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower107
  · exact lower103
def node513 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower513 : ∀ h, Pure node513 h → 11 ≤ h.length := by
  apply indexed_extend node513 [(5, node104), (6, node105), (7, node106)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower104
  · exact lower105
  · exact lower106
def node514 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 1], [0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower514 : ∀ h, Pure node514 h → 11 ≤ h.length := by
  apply indexed_extend node514 [(6, node107), (8, node104)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower107
  · exact lower104
def node515 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 2], [0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower515 : ∀ h, Pure node515 h → 11 ≤ h.length := by
  apply indexed_extend node515 [(8, node105), (12, node96)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower105
  · exact lower96
def entries128 : List Graph := [node512, node513, node514, node515]
theorem entries_count128 : entries128.length = 4 := by decide +kernel
theorem arc_count128 : (entries128.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by decide +kernel
end RawCert
