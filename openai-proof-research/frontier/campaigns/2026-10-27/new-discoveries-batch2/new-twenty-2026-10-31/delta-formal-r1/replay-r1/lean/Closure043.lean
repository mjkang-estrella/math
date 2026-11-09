import Closure042
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node172 : Graph := [[0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 1, 0, 0, 0, 2, 1, 0]]
theorem lower172 : ∀ h, Pure node172 h → 11 ≤ h.length := by
  apply indexed_extend node172 [(6, node14)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower14
def node173 : Graph := [[0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 2], [0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower173 : ∀ h, Pure node173 h → 11 ≤ h.length := by
  apply indexed_extend node173 [(4, node13)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower13
def node174 : Graph := [[0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0], [0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower174 : ∀ h, Pure node174 h → 11 ≤ h.length := by
  apply indexed_extend node174 [(5, node14)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower14
def node175 : Graph := [[0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 1, 1, 1, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower175 : ∀ h, Pure node175 h → 11 ≤ h.length := by
  apply indexed_extend node175 [(7, node13), (11, node12)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower13
  · exact lower12
def entries43 : List Graph := [node172, node173, node174, node175]
theorem entries_count43 : entries43.length = 4 := by decide +kernel
theorem arc_count43 : (entries43.map (fun g => ((verts g).filter (wye g)).length)).sum = 5 := by decide +kernel
end RawCert
