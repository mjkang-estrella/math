import Closure026
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node108 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower108 : ∀ h, Pure node108 h → 11 ≤ h.length := by
  apply indexed_extend node108 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node109 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 1, 0, 0, 2, 1, 0, 0]]
theorem lower109 : ∀ h, Pure node109 h → 11 ≤ h.length := by
  apply indexed_extend node109 [(8, node6)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower6
def node110 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0]]
theorem lower110 : ∀ h, Pure node110 h → 11 ≤ h.length := by
  apply indexed_extend node110 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node111 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 1, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1], [1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 2, 1, 0, 0]]
theorem lower111 : ∀ h, Pure node111 h → 11 ≤ h.length := by
  apply indexed_extend node111 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries27 : List Graph := [node108, node109, node110, node111]
theorem entries_count27 : entries27.length = 4 := by decide +kernel
theorem arc_count27 : (entries27.map (fun g => ((verts g).filter (wye g)).length)).sum = 1 := by decide +kernel
end RawCert
