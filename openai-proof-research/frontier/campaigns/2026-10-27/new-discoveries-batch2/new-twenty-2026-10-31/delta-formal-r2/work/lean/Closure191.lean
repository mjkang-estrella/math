import Closure190
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node764 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3], [2, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 1, 0, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower764 : ∀ h, Pure node764 h → 11 ≤ h.length := by
  apply indexed_extend node764 [(6, node200), (8, node190), (10, node240)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower200
  · exact lower190
  · exact lower240
def node765 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 1, 2, 0, 0, 0]]
theorem lower765 : ∀ h, Pure node765 h → 11 ≤ h.length := by
  apply indexed_extend node765 [(6, node201), (10, node241)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower201
  · exact lower241
def node766 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 1, 0, 1, 0, 1, 2, 0, 0, 0]]
theorem lower766 : ∀ h, Pure node766 h → 11 ≤ h.length := by
  apply indexed_extend node766 [(2, node165), (10, node242)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower165
  · exact lower242
def node767 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower767 : ∀ h, Pure node767 h → 11 ≤ h.length := by
  apply indexed_extend node767 [(6, node202), (8, node191)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower202
  · exact lower191
def entries191 : List Graph := [node764, node765, node766, node767]
theorem entries_count191 : entries191.length = 4 := by decide +kernel
theorem arc_count191 : (entries191.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by decide +kernel
end RawCert
