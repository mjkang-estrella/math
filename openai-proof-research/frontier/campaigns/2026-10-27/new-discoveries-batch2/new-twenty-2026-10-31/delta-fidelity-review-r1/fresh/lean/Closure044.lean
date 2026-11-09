import Closure043
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node176 : Graph := [[0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0], [0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0, 0]]
theorem lower176 : ∀ h, Pure node176 h → 11 ≤ h.length := by
  apply indexed_extend node176 [(7, node14)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower14
def node177 : Graph := [[0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3], [0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower177 : ∀ h, Pure node177 h → 11 ≤ h.length := by
  apply indexed_extend node177 [(2, node1)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower1
def node178 : Graph := [[0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower178 : ∀ h, Pure node178 h → 11 ≤ h.length := by
  apply indexed_extend node178 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node179 : Graph := [[0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0], [0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower179 : ∀ h, Pure node179 h → 11 ≤ h.length := by
  apply indexed_extend node179 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries44 : List Graph := [node176, node177, node178, node179]
theorem entries_count44 : entries44.length = 4 := by decide +kernel
theorem arc_count44 : (entries44.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
