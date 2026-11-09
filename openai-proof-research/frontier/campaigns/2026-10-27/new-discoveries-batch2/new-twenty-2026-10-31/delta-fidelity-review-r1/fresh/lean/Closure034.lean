import Closure033
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node136 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0], [1, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 1], [1, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0]]
theorem lower136 : ∀ h, Pure node136 h → 11 ≤ h.length := by
  apply indexed_extend node136 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node137 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1], [1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0]]
theorem lower137 : ∀ h, Pure node137 h → 11 ≤ h.length := by
  apply indexed_extend node137 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node138 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 2], [1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0]]
theorem lower138 : ∀ h, Pure node138 h → 11 ≤ h.length := by
  apply indexed_extend node138 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node139 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 2, 0]]
theorem lower139 : ∀ h, Pure node139 h → 11 ≤ h.length := by
  apply indexed_extend node139 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries34 : List Graph := [node136, node137, node138, node139]
theorem entries_count34 : entries34.length = 4 := by decide +kernel
theorem arc_count34 : (entries34.map (fun g => ((verts g).filter (wye g)).length)).sum = 0 := by decide +kernel
end RawCert
