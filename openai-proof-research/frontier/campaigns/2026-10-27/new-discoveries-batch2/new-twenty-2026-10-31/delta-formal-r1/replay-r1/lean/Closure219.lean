import Closure218
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node876 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 0]]
theorem lower876 : ∀ h, Pure node876 h → 11 ≤ h.length := by
  apply indexed_extend node876 [(4, node242), (10, node238)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower242
  · exact lower238
def node877 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0, 0]]
theorem lower877 : ∀ h, Pure node877 h → 11 ≤ h.length := by
  apply indexed_extend node877 [(4, node244), (9, node239)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower244
  · exact lower239
def node878 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0]]
theorem lower878 : ∀ h, Pure node878 h → 11 ≤ h.length := by
  apply indexed_extend node878 [(8, node243), (10, node241), (12, node240)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower243
  · exact lower241
  · exact lower240
def node879 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [1, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 2, 0, 0]]
theorem lower879 : ∀ h, Pure node879 h → 11 ≤ h.length := by
  apply indexed_extend node879 [(8, node244), (10, node242)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower244
  · exact lower242
def entries219 : List Graph := [node876, node877, node878, node879]
theorem entries_count219 : entries219.length = 4 := by decide +kernel
theorem arc_count219 : (entries219.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by decide +kernel
end RawCert
