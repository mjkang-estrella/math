import Closure054
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node220 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 3, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0]]
theorem lower220 : ∀ h, Pure node220 h → 11 ≤ h.length := by
  apply indexed_extend node220 [(6, node18)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower18
def node221 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0], [0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 1, 0], [1, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 2], [0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower221 : ∀ h, Pure node221 h → 11 ≤ h.length := by
  apply indexed_extend node221 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node222 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [1, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 1, 0]]
theorem lower222 : ∀ h, Pure node222 h → 11 ≤ h.length := by
  apply indexed_extend node222 [(6, node18)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower18
def node223 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [1, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 3, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0]]
theorem lower223 : ∀ h, Pure node223 h → 11 ≤ h.length := by
  apply indexed_extend node223 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries55 : List Graph := [node220, node221, node222, node223]
theorem entries_count55 : entries55.length = 4 := by decide +kernel
theorem arc_count55 : (entries55.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
