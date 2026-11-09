import Closure002
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node12 : Graph := [[0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3], [0, 0, 0, 1, 1, 1, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 3, 1, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower12 : ∀ h, Pure node12 h → 11 ≤ h.length := by
  apply indexed_extend node12 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node13 : Graph := [[0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 1, 1, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [0, 1, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 1, 0, 2, 2, 0, 0, 1, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower13 : ∀ h, Pure node13 h → 11 ≤ h.length := by
  apply indexed_extend node13 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node14 : Graph := [[0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0], [0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [1, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower14 : ∀ h, Pure node14 h → 11 ≤ h.length := by
  apply indexed_extend node14 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node15 : Graph := [[0, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3], [2, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [0, 0, 1, 0, 0, 0, 2, 1, 1, 1, 0], [0, 2, 0, 1, 0, 0, 0, 1, 0, 1, 1], [1, 0, 1, 1, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 2], [2, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower15 : ∀ h, Pure node15 h → 11 ≤ h.length := by
  apply indexed_extend node15 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries3 : List Graph := [node12, node13, node14, node15]
theorem entries_count3 : entries3.length = 4 := by decide +kernel
theorem arc_count3 : (entries3.map (fun g => ((verts g).filter (wye g)).length)).sum = 0 := by decide +kernel
end RawCert
