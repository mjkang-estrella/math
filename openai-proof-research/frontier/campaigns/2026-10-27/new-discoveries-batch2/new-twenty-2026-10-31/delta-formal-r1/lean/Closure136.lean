import Closure135
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node544 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [1, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower544 : ∀ h, Pure node544 h → 11 ≤ h.length := by
  apply indexed_extend node544 [(3, node74), (10, node136)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower74
  · exact lower136
def node545 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1, 0]]
theorem lower545 : ∀ h, Pure node545 h → 11 ≤ h.length := by
  apply indexed_extend node545 [(1, node199), (2, node198)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower199
  · exact lower198
def node546 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 1, 0, 0, 2, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower546 : ∀ h, Pure node546 h → 11 ≤ h.length := by
  apply indexed_extend node546 [(1, node200), (8, node113), (12, node109)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower200
  · exact lower113
  · exact lower109
def node547 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower547 : ∀ h, Pure node547 h → 11 ≤ h.length := by
  apply indexed_extend node547 [(1, node201), (11, node110)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower201
  · exact lower110
def entries136 : List Graph := [node544, node545, node546, node547]
theorem entries_count136 : entries136.length = 4 := by decide +kernel
theorem arc_count136 : (entries136.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by decide +kernel
end RawCert
