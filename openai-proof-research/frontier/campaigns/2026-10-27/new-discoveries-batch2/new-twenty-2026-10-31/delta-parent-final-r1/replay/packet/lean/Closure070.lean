import Closure069
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node280 : Graph := [[0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1], [0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 1], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3], [1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0]]
theorem lower280 : ∀ h, Pure node280 h → 11 ≤ h.length := by
  apply indexed_extend node280 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node281 : Graph := [[0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 1, 0, 0, 3, 0, 0], [1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 2], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower281 : ∀ h, Pure node281 h → 11 ≤ h.length := by
  apply indexed_extend node281 [(11, node24)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower24
def node282 : Graph := [[0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0], [1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0], [0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0]]
theorem lower282 : ∀ h, Pure node282 h → 11 ≤ h.length := by
  apply indexed_extend node282 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node283 : Graph := [[0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower283 : ∀ h, Pure node283 h → 11 ≤ h.length := by
  apply indexed_extend node283 [(2, node29), (4, node28), (8, node25)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower29
  · exact lower28
  · exact lower25
def entries70 : List Graph := [node280, node281, node282, node283]
theorem entries_count70 : entries70.length = 4 := by decide +kernel
theorem arc_count70 : (entries70.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by decide +kernel
end RawCert
