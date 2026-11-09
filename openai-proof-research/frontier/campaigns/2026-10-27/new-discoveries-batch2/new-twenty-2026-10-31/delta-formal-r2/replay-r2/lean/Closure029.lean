import Closure028
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node116 : Graph := [[0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0]]
theorem lower116 : ∀ h, Pure node116 h → 11 ≤ h.length := by
  apply indexed_extend node116 [(0, node23)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower23
def node117 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 1], [2, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 1], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 1], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0]]
theorem lower117 : ∀ h, Pure node117 h → 11 ≤ h.length := by
  apply indexed_extend node117 [(2, node17)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower17
def node118 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0], [2, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 1], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 2, 0]]
theorem lower118 : ∀ h, Pure node118 h → 11 ≤ h.length := by
  apply indexed_extend node118 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node119 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [2, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 1], [0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0]]
theorem lower119 : ∀ h, Pure node119 h → 11 ≤ h.length := by
  apply indexed_extend node119 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries29 : List Graph := [node116, node117, node118, node119]
theorem entries_count29 : entries29.length = 4 := by decide +kernel
theorem arc_count29 : (entries29.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
