import Closure001
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node8 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3], [0, 0, 0, 1, 0, 0, 0, 2, 1, 1, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 3, 1, 1, 0, 0, 1, 0]]
theorem lower8 : ∀ h, Pure node8 h → 11 ≤ h.length := by
  apply indexed_extend node8 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node9 : Graph := [[0, 0, 1, 0, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 1, 0, 2, 1], [1, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 1], [1, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0], [0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0]]
theorem lower9 : ∀ h, Pure node9 h → 11 ≤ h.length := by
  apply indexed_extend node9 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node10 : Graph := [[0, 0, 1, 0, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 1, 0, 2, 1], [1, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 2], [1, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0], [0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0]]
theorem lower10 : ∀ h, Pure node10 h → 11 ≤ h.length := by
  apply indexed_extend node10 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node11 : Graph := [[0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3], [1, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [1, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [0, 2, 1, 0, 0, 0, 0, 1, 0, 1, 1], [1, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 2], [3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower11 : ∀ h, Pure node11 h → 11 ≤ h.length := by
  apply indexed_extend node11 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries2 : List Graph := [node8, node9, node10, node11]
theorem entries_count2 : entries2.length = 4 := by decide +kernel
theorem arc_count2 : (entries2.map (fun g => ((verts g).filter (wye g)).length)).sum = 0 := by decide +kernel
end RawCert
