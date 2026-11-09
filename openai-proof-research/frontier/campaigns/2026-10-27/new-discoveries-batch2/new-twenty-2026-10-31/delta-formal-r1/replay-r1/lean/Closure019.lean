import Closure018
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node76 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0], [1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0]]
theorem lower76 : ∀ h, Pure node76 h → 11 ≤ h.length := by
  apply indexed_extend node76 [(7, node5)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower5
def node77 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 2], [0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0], [1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 0, 2, 0, 1, 0, 1, 0]]
theorem lower77 : ∀ h, Pure node77 h → 11 ≤ h.length := by
  apply indexed_extend node77 [(5, node4)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower4
def node78 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 1, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0], [0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0], [1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 0, 2, 0, 1, 0, 1, 0]]
theorem lower78 : ∀ h, Pure node78 h → 11 ≤ h.length := by
  apply indexed_extend node78 [(6, node5)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower5
def node79 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3], [0, 0, 0, 0, 1, 1, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower79 : ∀ h, Pure node79 h → 11 ≤ h.length := by
  apply indexed_extend node79 [(2, node12)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower12
def entries19 : List Graph := [node76, node77, node78, node79]
theorem entries_count19 : entries19.length = 4 := by decide +kernel
theorem arc_count19 : (entries19.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by decide +kernel
end RawCert
