import Closure129
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node520 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower520 : ∀ h, Pure node520 h → 11 ≤ h.length := by
  apply indexed_extend node520 [(2, node188), (8, node108)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower188
  · exact lower108
def node521 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower521 : ∀ h, Pure node521 h → 11 ≤ h.length := by
  apply indexed_extend node521 [(1, node188), (11, node98)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower188
  · exact lower98
def node522 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2], [0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower522 : ∀ h, Pure node522 h → 11 ≤ h.length := by
  apply indexed_extend node522 [(3, node69), (5, node109), (9, node99)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower69
  · exact lower109
  · exact lower99
def node523 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower523 : ∀ h, Pure node523 h → 11 ≤ h.length := by
  apply indexed_extend node523 [(3, node70), (5, node110)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower70
  · exact lower110
def entries130 : List Graph := [node520, node521, node522, node523]
theorem entries_count130 : entries130.length = 4 := by decide +kernel
theorem census_node520 : ((verts node520).filter (wye node520)).length = 2 := by decide +kernel
theorem census_node521 : ((verts node521).filter (wye node521)).length = 2 := by decide +kernel
theorem census_node522 : ((verts node522).filter (wye node522)).length = 3 := by decide +kernel
theorem census_node523 : ((verts node523).filter (wye node523)).length = 2 := by decide +kernel
theorem arc_count130 : (entries130.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries130, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node520, census_node521, census_node522, census_node523]
  decide +kernel
end RawCert
