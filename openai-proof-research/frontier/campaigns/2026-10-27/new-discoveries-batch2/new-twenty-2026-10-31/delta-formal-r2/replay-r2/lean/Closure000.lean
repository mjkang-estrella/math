import RawClosure
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node0 : Graph := [[0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3], [0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0], [2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1], [0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower0 : ∀ h, Pure node0 h → 11 ≤ h.length := by
  apply indexed_extend node0 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node1 : Graph := [[0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 0], [2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 1, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 3, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower1 : ∀ h, Pure node1 h → 11 ≤ h.length := by
  apply indexed_extend node1 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node2 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 1], [0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0]]
theorem lower2 : ∀ h, Pure node2 h → 11 ≤ h.length := by
  apply indexed_extend node2 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node3 : Graph := [[0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0], [0, 0, 3, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1], [0, 2, 1, 1, 0, 0, 0, 0, 1, 0, 1], [1, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 1], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0]]
theorem lower3 : ∀ h, Pure node3 h → 11 ≤ h.length := by
  apply indexed_extend node3 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries0 : List Graph := [node0, node1, node2, node3]
theorem entries_count0 : entries0.length = 4 := by decide +kernel
theorem arc_count0 : (entries0.map (fun g => ((verts g).filter (wye g)).length)).sum = 0 := by decide +kernel
end RawCert
