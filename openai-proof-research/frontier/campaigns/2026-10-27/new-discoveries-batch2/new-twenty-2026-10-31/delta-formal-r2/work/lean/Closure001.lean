import Closure000
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node4 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 0, 1, 1, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 2], [0, 1, 0, 0, 2, 2, 0, 0, 1, 0, 0], [1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 1, 1, 0, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0]]
theorem lower4 : ∀ h, Pure node4 h → 11 ≤ h.length := by
  apply indexed_extend node4 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node5 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 1, 2, 0, 0, 1, 1, 0, 1, 0, 0], [0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 1], [1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0]]
theorem lower5 : ∀ h, Pure node5 h → 11 ≤ h.length := by
  apply indexed_extend node5 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node6 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 2, 0], [0, 0, 3, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3], [0, 0, 0, 1, 0, 0, 0, 2, 1, 1, 1], [0, 2, 1, 0, 1, 0, 0, 0, 1, 0, 1], [1, 0, 0, 1, 1, 2, 0, 0, 0, 1, 0], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 1], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0]]
theorem lower6 : ∀ h, Pure node6 h → 11 ≤ h.length := by
  apply indexed_extend node6 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node7 : Graph := [[0, 0, 0, 2, 1, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 2, 1], [2, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0], [1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1], [0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [0, 1, 1, 1, 0, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower7 : ∀ h, Pure node7 h → 11 ≤ h.length := by
  apply indexed_extend node7 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries1 : List Graph := [node4, node5, node6, node7]
theorem entries_count1 : entries1.length = 4 := by decide +kernel
theorem arc_count1 : (entries1.map (fun g => ((verts g).filter (wye g)).length)).sum = 0 := by decide +kernel
end RawCert
