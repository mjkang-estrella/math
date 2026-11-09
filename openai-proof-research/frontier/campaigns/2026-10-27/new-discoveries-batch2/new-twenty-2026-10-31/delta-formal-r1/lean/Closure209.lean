import Closure208
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node836 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower836 : ∀ h, Pure node836 h → 11 ≤ h.length := by
  apply indexed_extend node836 [(4, node243), (12, node217)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower243
  · exact lower217
def node837 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [1, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0, 0]]
theorem lower837 : ∀ h, Pure node837 h → 11 ≤ h.length := by
  apply indexed_extend node837 [(3, node252), (8, node219), (10, node218)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower252
  · exact lower219
  · exact lower218
def node838 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0, 0]]
theorem lower838 : ∀ h, Pure node838 h → 11 ≤ h.length := by
  apply indexed_extend node838 [(4, node244), (8, node219)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower244
  · exact lower219
def node839 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower839 : ∀ h, Pure node839 h → 11 ≤ h.length := by
  apply indexed_extend node839 [(6, node224)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower224
def entries209 : List Graph := [node836, node837, node838, node839]
theorem entries_count209 : entries209.length = 4 := by decide +kernel
theorem arc_count209 : (entries209.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by decide +kernel
end RawCert
