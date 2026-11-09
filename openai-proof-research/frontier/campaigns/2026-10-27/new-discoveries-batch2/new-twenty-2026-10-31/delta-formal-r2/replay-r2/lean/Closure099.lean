import Closure098
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node396 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 1, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 2, 0, 0]]
theorem lower396 : ∀ h, Pure node396 h → 11 ≤ h.length := by
  apply indexed_extend node396 [(8, node61)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower61
def node397 : Graph := [[0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0]]
theorem lower397 : ∀ h, Pure node397 h → 11 ≤ h.length := by
  apply indexed_extend node397 [(4, node68), (8, node62)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower68
  · exact lower62
def node398 : Graph := [[0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower398 : ∀ h, Pure node398 h → 11 ≤ h.length := by
  apply indexed_extend node398 [(4, node69), (7, node63), (9, node62)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower69
  · exact lower63
  · exact lower62
def node399 : Graph := [[0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower399 : ∀ h, Pure node399 h → 11 ≤ h.length := by
  apply indexed_extend node399 [(4, node70), (7, node65)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower70
  · exact lower65
def entries99 : List Graph := [node396, node397, node398, node399]
theorem entries_count99 : entries99.length = 4 := by decide +kernel
theorem arc_count99 : (entries99.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by decide +kernel
end RawCert
