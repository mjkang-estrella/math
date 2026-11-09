import Closure197
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node792 : Graph := [[0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0], [0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower792 : ∀ h, Pure node792 h → 11 ≤ h.length := by
  apply indexed_extend node792 [(0, node39), (2, node188), (9, node252)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower39
  · exact lower188
  · exact lower252
def node793 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 1, 0], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 2], [0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower793 : ∀ h, Pure node793 h → 11 ≤ h.length := by
  apply indexed_extend node793 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node794 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 1, 0]]
theorem lower794 : ∀ h, Pure node794 h → 11 ≤ h.length := by
  apply indexed_extend node794 [(7, node207), (8, node209)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower207
  · exact lower209
def node795 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 1, 0]]
theorem lower795 : ∀ h, Pure node795 h → 11 ≤ h.length := by
  apply indexed_extend node795 [(7, node208)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower208
def entries198 : List Graph := [node792, node793, node794, node795]
theorem entries_count198 : entries198.length = 4 := by decide +kernel
theorem arc_count198 : (entries198.map (fun g => ((verts g).filter (wye g)).length)).sum = 6 := by decide +kernel
end RawCert
