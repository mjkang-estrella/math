import Closure048
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node196 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower196 : ∀ h, Pure node196 h → 11 ≤ h.length := by
  apply indexed_extend node196 [(4, node15)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower15
def node197 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 2, 0, 1, 0], [1, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 2, 0, 0, 1, 0, 1, 0]]
theorem lower197 : ∀ h, Pure node197 h → 11 ≤ h.length := by
  apply indexed_extend node197 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node198 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1, 0]]
theorem lower198 : ∀ h, Pure node198 h → 11 ≤ h.length := by
  apply indexed_extend node198 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node199 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1, 0]]
theorem lower199 : ∀ h, Pure node199 h → 11 ≤ h.length := by
  apply indexed_extend node199 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries49 : List Graph := [node196, node197, node198, node199]
theorem entries_count49 : entries49.length = 4 := by decide +kernel
theorem arc_count49 : (entries49.map (fun g => ((verts g).filter (wye g)).length)).sum = 1 := by decide +kernel
end RawCert
