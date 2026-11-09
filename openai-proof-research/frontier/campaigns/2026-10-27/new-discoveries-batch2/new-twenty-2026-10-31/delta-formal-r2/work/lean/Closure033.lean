import Closure032
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node132 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 1, 0]]
theorem lower132 : ∀ h, Pure node132 h → 11 ≤ h.length := by
  apply indexed_extend node132 [(9, node8)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower8
def node133 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 2, 0]]
theorem lower133 : ∀ h, Pure node133 h → 11 ≤ h.length := by
  apply indexed_extend node133 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node134 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 1], [1, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 2, 0]]
theorem lower134 : ∀ h, Pure node134 h → 11 ≤ h.length := by
  apply indexed_extend node134 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node135 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0]]
theorem lower135 : ∀ h, Pure node135 h → 11 ≤ h.length := by
  apply indexed_extend node135 [(11, node8)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower8
def entries33 : List Graph := [node132, node133, node134, node135]
theorem entries_count33 : entries33.length = 4 := by decide +kernel
theorem arc_count33 : (entries33.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
