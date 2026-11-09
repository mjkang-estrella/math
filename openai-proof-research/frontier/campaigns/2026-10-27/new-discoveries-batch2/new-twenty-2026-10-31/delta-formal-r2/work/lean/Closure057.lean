import Closure056
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node228 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3], [3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1, 0], [0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0]]
theorem lower228 : ∀ h, Pure node228 h → 11 ≤ h.length := by
  apply indexed_extend node228 [(4, node19)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower19
def node229 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0]]
theorem lower229 : ∀ h, Pure node229 h → 11 ≤ h.length := by
  apply indexed_extend node229 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node230 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 2, 0, 0, 0, 1, 1, 0]]
theorem lower230 : ∀ h, Pure node230 h → 11 ≤ h.length := by
  apply indexed_extend node230 [(6, node20)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower20
def node231 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1, 0]]
theorem lower231 : ∀ h, Pure node231 h → 11 ≤ h.length := by
  apply indexed_extend node231 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries57 : List Graph := [node228, node229, node230, node231]
theorem entries_count57 : entries57.length = 4 := by decide +kernel
theorem arc_count57 : (entries57.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
