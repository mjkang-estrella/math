import Closure008
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node36 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 1], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0]]
theorem lower36 : ∀ h, Pure node36 h → 11 ≤ h.length := by
  apply indexed_extend node36 [(2, node2)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower2
def node37 : Graph := [[0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3], [0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower37 : ∀ h, Pure node37 h → 11 ≤ h.length := by
  apply indexed_extend node37 [(5, node1)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower1
def node38 : Graph := [[0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0, 0], [0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 1, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 3, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower38 : ∀ h, Pure node38 h → 11 ≤ h.length := by
  apply indexed_extend node38 [(11, node1)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower1
def node39 : Graph := [[0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0], [0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 3, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower39 : ∀ h, Pure node39 h → 11 ≤ h.length := by
  apply indexed_extend node39 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries9 : List Graph := [node36, node37, node38, node39]
theorem entries_count9 : entries9.length = 4 := by decide +kernel
theorem arc_count9 : (entries9.map (fun g => ((verts g).filter (wye g)).length)).sum = 3 := by decide +kernel
end RawCert
