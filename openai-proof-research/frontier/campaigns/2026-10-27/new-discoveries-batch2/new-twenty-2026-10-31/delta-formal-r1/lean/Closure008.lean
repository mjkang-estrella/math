import Closure007
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node32 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 2, 0, 1, 0, 1, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 1, 0, 1, 1, 2, 0, 0, 0]]
theorem lower32 : ∀ h, Pure node32 h → 11 ≤ h.length := by
  apply indexed_extend node32 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node33 : Graph := [[0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [0, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower33 : ∀ h, Pure node33 h → 11 ≤ h.length := by
  apply indexed_extend node33 [(11, node0)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower0
def node34 : Graph := [[0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [0, 1, 2, 0, 1, 0, 1, 0, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 2, 0, 2, 0, 0]]
theorem lower34 : ∀ h, Pure node34 h → 11 ≤ h.length := by
  apply indexed_extend node34 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node35 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0], [0, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1, 1, 1, 2, 0, 0]]
theorem lower35 : ∀ h, Pure node35 h → 11 ≤ h.length := by
  apply indexed_extend node35 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries8 : List Graph := [node32, node33, node34, node35]
theorem entries_count8 : entries8.length = 4 := by decide +kernel
theorem arc_count8 : (entries8.map (fun g => ((verts g).filter (wye g)).length)).sum = 1 := by decide +kernel
end RawCert
