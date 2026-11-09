import Closure130
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node524 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower524 : ∀ h, Pure node524 h → 11 ≤ h.length := by
  apply indexed_extend node524 [(5, node109), (7, node111), (9, node100)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower109
  · exact lower111
  · exact lower100
def node525 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower525 : ∀ h, Pure node525 h → 11 ≤ h.length := by
  apply indexed_extend node525 [(5, node110), (7, node112)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower110
  · exact lower112
def node526 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 1, 0, 0]]
theorem lower526 : ∀ h, Pure node526 h → 11 ≤ h.length := by
  apply indexed_extend node526 [(7, node109), (9, node101), (11, node132)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower109
  · exact lower101
  · exact lower132
def node527 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower527 : ∀ h, Pure node527 h → 11 ≤ h.length := by
  apply indexed_extend node527 [(7, node110), (11, node133)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower110
  · exact lower133
def entries131 : List Graph := [node524, node525, node526, node527]
theorem entries_count131 : entries131.length = 4 := by decide +kernel
theorem arc_count131 : (entries131.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by decide +kernel
end RawCert
