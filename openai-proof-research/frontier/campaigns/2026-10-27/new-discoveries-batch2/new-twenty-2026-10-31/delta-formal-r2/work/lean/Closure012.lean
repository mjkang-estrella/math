import Closure011
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node48 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0], [0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 0, 2, 0, 1, 0, 1, 0]]
theorem lower48 : ∀ h, Pure node48 h → 11 ≤ h.length := by
  apply indexed_extend node48 [(6, node2)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower2
def node49 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 1, 1, 2, 0, 0, 0]]
theorem lower49 : ∀ h, Pure node49 h → 11 ≤ h.length := by
  apply indexed_extend node49 [(8, node2)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower2
def node50 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]]
theorem lower50 : ∀ h, Pure node50 h → 11 ≤ h.length := by
  apply indexed_extend node50 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node51 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0, 1], [0, 2, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 2, 0]]
theorem lower51 : ∀ h, Pure node51 h → 11 ≤ h.length := by
  apply indexed_extend node51 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries12 : List Graph := [node48, node49, node50, node51]
theorem entries_count12 : entries12.length = 4 := by decide +kernel
theorem arc_count12 : (entries12.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
