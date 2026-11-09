import Closure029
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node120 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0]]
theorem lower120 : ∀ h, Pure node120 h → 11 ≤ h.length := by
  apply indexed_extend node120 [(5, node8)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower8
def node121 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 1], [2, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2, 0]]
theorem lower121 : ∀ h, Pure node121 h → 11 ≤ h.length := by
  apply indexed_extend node121 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node122 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0], [1, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 2], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 2, 0]]
theorem lower122 : ∀ h, Pure node122 h → 11 ≤ h.length := by
  apply indexed_extend node122 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node123 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1], [0, 0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 1], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0]]
theorem lower123 : ∀ h, Pure node123 h → 11 ≤ h.length := by
  apply indexed_extend node123 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries30 : List Graph := [node120, node121, node122, node123]
theorem entries_count30 : entries30.length = 4 := by decide +kernel
theorem arc_count30 : (entries30.map (fun g => ((verts g).filter (wye g)).length)).sum = 1 := by decide +kernel
end RawCert
