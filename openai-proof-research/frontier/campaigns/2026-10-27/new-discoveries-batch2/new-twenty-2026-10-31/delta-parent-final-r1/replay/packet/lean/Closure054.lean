import Closure053
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node216 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 3], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 1, 0], [0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1], [1, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 2], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0]]
theorem lower216 : ∀ h, Pure node216 h → 11 ≤ h.length := by
  apply indexed_extend node216 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node217 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0], [0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0]]
theorem lower217 : ∀ h, Pure node217 h → 11 ≤ h.length := by
  apply indexed_extend node217 [(4, node19)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower19
def node218 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0], [1, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1, 1, 2, 0, 0]]
theorem lower218 : ∀ h, Pure node218 h → 11 ≤ h.length := by
  apply indexed_extend node218 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node219 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0], [1, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 2, 2, 0, 0]]
theorem lower219 : ∀ h, Pure node219 h → 11 ≤ h.length := by
  apply indexed_extend node219 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries54 : List Graph := [node216, node217, node218, node219]
theorem entries_count54 : entries54.length = 4 := by decide +kernel
theorem arc_count54 : (entries54.map (fun g => ((verts g).filter (wye g)).length)).sum = 1 := by decide +kernel
end RawCert
