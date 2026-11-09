import Closure205
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node824 : Graph := [[0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 2, 0, 0]]
theorem lower824 : ∀ h, Pure node824 h → 11 ≤ h.length := by
  apply indexed_extend node824 [(3, node227), (9, node214), (10, node215)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower227
  · exact lower214
  · exact lower215
def node825 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0], [2, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1], [1, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0]]
theorem lower825 : ∀ h, Pure node825 h → 11 ≤ h.length := by
  apply indexed_extend node825 [(3, node250), (9, node216)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower250
  · exact lower216
def node826 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1, 0], [0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0]]
theorem lower826 : ∀ h, Pure node826 h → 11 ≤ h.length := by
  apply indexed_extend node826 [(4, node228), (5, node217), (9, node216)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower228
  · exact lower217
  · exact lower216
def node827 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 3, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0], [1, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 2], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower827 : ∀ h, Pure node827 h → 11 ≤ h.length := by
  apply indexed_extend node827 [(6, node218)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower218
def entries206 : List Graph := [node824, node825, node826, node827]
theorem entries_count206 : entries206.length = 4 := by decide +kernel
theorem arc_count206 : (entries206.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by decide +kernel
end RawCert
