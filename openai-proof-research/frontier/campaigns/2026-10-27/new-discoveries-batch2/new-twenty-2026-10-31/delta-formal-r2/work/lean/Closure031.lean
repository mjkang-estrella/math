import Closure030
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node124 : Graph := [[0, 0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 1, 1], [2, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 1, 0, 2, 1, 0]]
theorem lower124 : ∀ h, Pure node124 h → 11 ≤ h.length := by
  apply indexed_extend node124 [(2, node18)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower18
def node125 : Graph := [[0, 0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1], [1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0]]
theorem lower125 : ∀ h, Pure node125 h → 11 ≤ h.length := by
  apply indexed_extend node125 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node126 : Graph := [[0, 0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 3, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 2, 0]]
theorem lower126 : ∀ h, Pure node126 h → 11 ≤ h.length := by
  apply indexed_extend node126 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node127 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0]]
theorem lower127 : ∀ h, Pure node127 h → 11 ≤ h.length := by
  apply indexed_extend node127 [(5, node8)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower8
def entries31 : List Graph := [node124, node125, node126, node127]
theorem entries_count31 : entries31.length = 4 := by decide +kernel
theorem arc_count31 : (entries31.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
