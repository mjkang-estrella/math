import Closure014
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node60 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0], [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]]
theorem lower60 : ∀ h, Pure node60 h → 11 ≤ h.length := by
  apply indexed_extend node60 [(6, node5)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower5
def node61 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0]]
theorem lower61 : ∀ h, Pure node61 h → 11 ≤ h.length := by
  apply indexed_extend node61 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node62 : Graph := [[0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0], [0, 1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower62 : ∀ h, Pure node62 h → 11 ≤ h.length := by
  apply indexed_extend node62 [(4, node3)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower3
def node63 : Graph := [[0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0], [0, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0], [1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2], [0, 1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0]]
theorem lower63 : ∀ h, Pure node63 h → 11 ≤ h.length := by
  apply indexed_extend node63 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries15 : List Graph := [node60, node61, node62, node63]
theorem entries_count15 : entries15.length = 4 := by decide +kernel
theorem arc_count15 : (entries15.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
