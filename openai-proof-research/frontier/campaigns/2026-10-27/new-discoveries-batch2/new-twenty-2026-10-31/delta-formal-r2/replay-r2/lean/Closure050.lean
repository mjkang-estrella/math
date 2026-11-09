import Closure049
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node200 : Graph := [[0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [2, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [1, 0, 1, 1, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 1, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower200 : ∀ h, Pure node200 h → 11 ≤ h.length := by
  apply indexed_extend node200 [(7, node15)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower15
def node201 : Graph := [[0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 2], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [1, 0, 1, 1, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower201 : ∀ h, Pure node201 h → 11 ≤ h.length := by
  apply indexed_extend node201 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node202 : Graph := [[0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [2, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 0], [1, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower202 : ∀ h, Pure node202 h → 11 ≤ h.length := by
  apply indexed_extend node202 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node203 : Graph := [[0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 2], [1, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 1, 2, 0, 0, 0]]
theorem lower203 : ∀ h, Pure node203 h → 11 ≤ h.length := by
  apply indexed_extend node203 [(8, node16)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower16
def entries50 : List Graph := [node200, node201, node202, node203]
theorem entries_count50 : entries50.length = 4 := by decide +kernel
theorem arc_count50 : (entries50.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
