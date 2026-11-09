import Closure121
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node488 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower488 : ∀ h, Pure node488 h → 11 ≤ h.length := by
  apply indexed_extend node488 [(3, node162), (7, node93), (8, node94)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower162
  · exact lower93
  · exact lower94
def node489 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower489 : ∀ h, Pure node489 h → 11 ≤ h.length := by
  apply indexed_extend node489 [(3, node164)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower164
def node490 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower490 : ∀ h, Pure node490 h → 11 ≤ h.length := by
  apply indexed_extend node490 [(5, node95)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower95
def node491 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 0, 0]]
theorem lower491 : ∀ h, Pure node491 h → 11 ≤ h.length := by
  apply indexed_extend node491 [(3, node165), (7, node95)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower165
  · exact lower95
def entries122 : List Graph := [node488, node489, node490, node491]
theorem entries_count122 : entries122.length = 4 := by decide +kernel
theorem arc_count122 : (entries122.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by decide +kernel
end RawCert
