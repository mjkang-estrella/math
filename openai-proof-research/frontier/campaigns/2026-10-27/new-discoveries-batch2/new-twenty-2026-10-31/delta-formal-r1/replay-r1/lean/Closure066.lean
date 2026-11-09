import Closure065
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node264 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2], [0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower264 : ∀ h, Pure node264 h → 11 ≤ h.length := by
  apply indexed_extend node264 [(3, node23), (8, node22)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower23
  · exact lower22
def node265 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 2], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower265 : ∀ h, Pure node265 h → 11 ≤ h.length := by
  apply indexed_extend node265 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node266 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 0, 1, 2, 0, 1, 0, 1, 0, 0, 1, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 1], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1, 1, 2, 0, 0]]
theorem lower266 : ∀ h, Pure node266 h → 11 ≤ h.length := by
  apply indexed_extend node266 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node267 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1], [0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 3, 1, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0]]
theorem lower267 : ∀ h, Pure node267 h → 11 ≤ h.length := by
  apply indexed_extend node267 [(4, node23)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower23
def entries66 : List Graph := [node264, node265, node266, node267]
theorem entries_count66 : entries66.length = 4 := by decide +kernel
theorem arc_count66 : (entries66.map (fun g => ((verts g).filter (wye g)).length)).sum = 3 := by decide +kernel
end RawCert
