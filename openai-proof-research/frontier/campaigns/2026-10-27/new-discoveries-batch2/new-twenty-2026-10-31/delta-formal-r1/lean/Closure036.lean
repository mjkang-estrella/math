import Closure035
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node144 : Graph := [[0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower144 : ∀ h, Pure node144 h → 11 ≤ h.length := by
  apply indexed_extend node144 [(5, node13)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower13
def node145 : Graph := [[0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0], [0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower145 : ∀ h, Pure node145 h → 11 ≤ h.length := by
  apply indexed_extend node145 [(5, node14)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower14
def node146 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower146 : ∀ h, Pure node146 h → 11 ≤ h.length := by
  apply indexed_extend node146 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node147 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower147 : ∀ h, Pure node147 h → 11 ≤ h.length := by
  apply indexed_extend node147 [(6, node10)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower10
def entries36 : List Graph := [node144, node145, node146, node147]
theorem entries_count36 : entries36.length = 4 := by decide +kernel
theorem arc_count36 : (entries36.map (fun g => ((verts g).filter (wye g)).length)).sum = 3 := by decide +kernel
end RawCert
