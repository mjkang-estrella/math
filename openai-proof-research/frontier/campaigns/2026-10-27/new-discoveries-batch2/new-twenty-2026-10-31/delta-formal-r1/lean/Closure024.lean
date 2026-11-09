import Closure023
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node96 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower96 : ∀ h, Pure node96 h → 11 ≤ h.length := by
  apply indexed_extend node96 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node97 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [2, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0], [1, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower97 : ∀ h, Pure node97 h → 11 ≤ h.length := by
  apply indexed_extend node97 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node98 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 1], [0, 2, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower98 : ∀ h, Pure node98 h → 11 ≤ h.length := by
  apply indexed_extend node98 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node99 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3], [0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1], [1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0]]
theorem lower99 : ∀ h, Pure node99 h → 11 ≤ h.length := by
  apply indexed_extend node99 [(3, node3), (5, node6)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower3
  · exact lower6
def entries24 : List Graph := [node96, node97, node98, node99]
theorem entries_count24 : entries24.length = 4 := by decide +kernel
theorem arc_count24 : (entries24.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
