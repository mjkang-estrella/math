import Closure045
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node184 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [2, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 0, 1, 0, 2, 2, 0, 0, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower184 : ∀ h, Pure node184 h → 11 ≤ h.length := by
  apply indexed_extend node184 [(0, node13)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower13
def node185 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [2, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower185 : ∀ h, Pure node185 h → 11 ≤ h.length := by
  apply indexed_extend node185 [(0, node14), (2, node7), (8, node18)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower14
  · exact lower7
  · exact lower18
def node186 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower186 : ∀ h, Pure node186 h → 11 ≤ h.length := by
  apply indexed_extend node186 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node187 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [2, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0], [1, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower187 : ∀ h, Pure node187 h → 11 ≤ h.length := by
  apply indexed_extend node187 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries46 : List Graph := [node184, node185, node186, node187]
theorem entries_count46 : entries46.length = 4 := by decide +kernel
theorem arc_count46 : (entries46.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by decide +kernel
end RawCert
