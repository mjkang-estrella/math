import Closure100
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node404 : Graph := [[0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower404 : ∀ h, Pure node404 h → 11 ≤ h.length := by
  apply indexed_extend node404 [(1, node151), (2, node147), (7, node67)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower151
  · exact lower147
  · exact lower67
def node405 : Graph := [[0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0]]
theorem lower405 : ∀ h, Pure node405 h → 11 ≤ h.length := by
  apply indexed_extend node405 [(1, node152), (2, node148), (6, node66)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower152
  · exact lower148
  · exact lower66
def node406 : Graph := [[0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower406 : ∀ h, Pure node406 h → 11 ≤ h.length := by
  apply indexed_extend node406 [(2, node149), (6, node66), (7, node67)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower149
  · exact lower66
  · exact lower67
def node407 : Graph := [[0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower407 : ∀ h, Pure node407 h → 11 ≤ h.length := by
  apply indexed_extend node407 [(4, node73), (12, node62)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower73
  · exact lower62
def entries101 : List Graph := [node404, node405, node406, node407]
theorem entries_count101 : entries101.length = 4 := by decide +kernel
theorem arc_count101 : (entries101.map (fun g => ((verts g).filter (wye g)).length)).sum = 11 := by decide +kernel
end RawCert
