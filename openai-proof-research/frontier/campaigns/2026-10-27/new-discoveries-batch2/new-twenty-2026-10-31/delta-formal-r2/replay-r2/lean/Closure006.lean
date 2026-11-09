import Closure005
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node24 : Graph := [[0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 1, 1, 0, 0, 3, 0], [1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1], [0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3], [1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 3, 1, 0, 0]]
theorem lower24 : ∀ h, Pure node24 h → 11 ≤ h.length := by
  apply indexed_extend node24 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node25 : Graph := [[0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower25 : ∀ h, Pure node25 h → 11 ≤ h.length := by
  apply indexed_extend node25 [(4, node0)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower0
def node26 : Graph := [[0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 1, 2, 0, 1, 0, 0, 1, 0, 1, 0, 0], [0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 0], [2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower26 : ∀ h, Pure node26 h → 11 ≤ h.length := by
  apply indexed_extend node26 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node27 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 1, 0, 1, 0], [2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower27 : ∀ h, Pure node27 h → 11 ≤ h.length := by
  apply indexed_extend node27 [(6, node0)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower0
def entries6 : List Graph := [node24, node25, node26, node27]
theorem entries_count6 : entries6.length = 4 := by decide +kernel
theorem arc_count6 : (entries6.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
