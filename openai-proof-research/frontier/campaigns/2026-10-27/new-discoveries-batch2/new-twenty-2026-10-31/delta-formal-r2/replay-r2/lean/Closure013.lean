import Closure012
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node52 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0]]
theorem lower52 : ∀ h, Pure node52 h → 11 ≤ h.length := by
  apply indexed_extend node52 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node53 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 1], [0, 2, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0]]
theorem lower53 : ∀ h, Pure node53 h → 11 ≤ h.length := by
  apply indexed_extend node53 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node54 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [0, 1, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower54 : ∀ h, Pure node54 h → 11 ≤ h.length := by
  apply indexed_extend node54 [(2, node7), (9, node2)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower7
  · exact lower2
def node55 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 1], [0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0]]
theorem lower55 : ∀ h, Pure node55 h → 11 ≤ h.length := by
  apply indexed_extend node55 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries13 : List Graph := [node52, node53, node54, node55]
theorem entries_count13 : entries13.length = 4 := by decide +kernel
theorem arc_count13 : (entries13.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
