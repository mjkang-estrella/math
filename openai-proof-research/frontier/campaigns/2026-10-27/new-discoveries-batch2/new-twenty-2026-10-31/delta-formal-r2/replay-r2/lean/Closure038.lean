import Closure037
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node152 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0]]
theorem lower152 : ∀ h, Pure node152 h → 11 ≤ h.length := by
  apply indexed_extend node152 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node153 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 3, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [1, 0, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 2], [0, 2, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower153 : ∀ h, Pure node153 h → 11 ≤ h.length := by
  apply indexed_extend node153 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node154 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 3, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [1, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 1], [0, 2, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 1], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower154 : ∀ h, Pure node154 h → 11 ≤ h.length := by
  apply indexed_extend node154 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node155 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 2], [0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower155 : ∀ h, Pure node155 h → 11 ≤ h.length := by
  apply indexed_extend node155 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries38 : List Graph := [node152, node153, node154, node155]
theorem entries_count38 : entries38.length = 4 := by decide +kernel
theorem arc_count38 : (entries38.map (fun g => ((verts g).filter (wye g)).length)).sum = 0 := by decide +kernel
end RawCert
