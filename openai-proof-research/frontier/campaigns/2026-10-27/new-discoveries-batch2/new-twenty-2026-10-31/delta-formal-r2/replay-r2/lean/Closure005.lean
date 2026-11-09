import Closure004
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node20 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 3, 0], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 1], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 2], [1, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 2, 0, 0, 1, 1, 0]]
theorem lower20 : ∀ h, Pure node20 h → 11 ≤ h.length := by
  apply indexed_extend node20 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node21 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 3, 0], [3, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 1], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1], [1, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0]]
theorem lower21 : ∀ h, Pure node21 h → 11 ≤ h.length := by
  apply indexed_extend node21 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node22 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3], [0, 0, 1, 2, 0, 0, 0, 2, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1], [2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0], [1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 1], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0], [0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0]]
theorem lower22 : ∀ h, Pure node22 h → 11 ≤ h.length := by
  apply indexed_extend node22 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node23 : Graph := [[0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1], [0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1], [2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3], [1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 3, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0]]
theorem lower23 : ∀ h, Pure node23 h → 11 ≤ h.length := by
  apply indexed_extend node23 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries5 : List Graph := [node20, node21, node22, node23]
theorem entries_count5 : entries5.length = 4 := by decide +kernel
theorem arc_count5 : (entries5.map (fun g => ((verts g).filter (wye g)).length)).sum = 0 := by decide +kernel
end RawCert
