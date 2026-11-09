import Closure066
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node268 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1], [0, 0, 2, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 3, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0]]
theorem lower268 : ∀ h, Pure node268 h → 11 ≤ h.length := by
  apply indexed_extend node268 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node269 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3], [1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0]]
theorem lower269 : ∀ h, Pure node269 h → 11 ≤ h.length := by
  apply indexed_extend node269 [(3, node23), (6, node24)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower23
  · exact lower24
def node270 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [0, 0, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 2], [2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower270 : ∀ h, Pure node270 h → 11 ≤ h.length := by
  apply indexed_extend node270 [(11, node22)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower22
def node271 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [0, 0, 1, 2, 0, 1, 0, 1, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1], [2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 2, 0]]
theorem lower271 : ∀ h, Pure node271 h → 11 ≤ h.length := by
  apply indexed_extend node271 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries67 : List Graph := [node268, node269, node270, node271]
theorem entries_count67 : entries67.length = 4 := by decide +kernel
theorem arc_count67 : (entries67.map (fun g => ((verts g).filter (wye g)).length)).sum = 3 := by decide +kernel
end RawCert
