import Closure031
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node128 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0], [0, 1, 1, 0, 0, 2, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0]]
theorem lower128 : ∀ h, Pure node128 h → 11 ≤ h.length := by
  apply indexed_extend node128 [(5, node8)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower8
def node129 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 1, 1, 0], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 0, 0, 0, 3, 1, 1, 0, 0, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower129 : ∀ h, Pure node129 h → 11 ≤ h.length := by
  apply indexed_extend node129 [(1, node19), (11, node8)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower19
  · exact lower8
def node130 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 1], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 2], [1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 1], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 2, 0, 0, 1, 1, 0]]
theorem lower130 : ∀ h, Pure node130 h → 11 ≤ h.length := by
  apply indexed_extend node130 [(2, node20)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower20
def node131 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 1], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 1], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0]]
theorem lower131 : ∀ h, Pure node131 h → 11 ≤ h.length := by
  apply indexed_extend node131 [(2, node21)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower21
def entries32 : List Graph := [node128, node129, node130, node131]
theorem entries_count32 : entries32.length = 4 := by decide +kernel
theorem arc_count32 : (entries32.map (fun g => ((verts g).filter (wye g)).length)).sum = 5 := by decide +kernel
end RawCert
