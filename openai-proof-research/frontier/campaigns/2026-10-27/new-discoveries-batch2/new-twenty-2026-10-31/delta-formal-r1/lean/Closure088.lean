import Closure087
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node352 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower352 : ∀ h, Pure node352 h → 11 ≤ h.length := by
  apply indexed_extend node352 [(6, node51), (12, node41)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower51
  · exact lower41
def node353 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower353 : ∀ h, Pure node353 h → 11 ≤ h.length := by
  apply indexed_extend node353 [(3, node98), (8, node51), (11, node42)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower98
  · exact lower51
  · exact lower42
def node354 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1], [0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower354 : ∀ h, Pure node354 h → 11 ≤ h.length := by
  apply indexed_extend node354 [(4, node74), (8, node51)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower74
  · exact lower51
def node355 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower355 : ∀ h, Pure node355 h → 11 ≤ h.length := by
  apply indexed_extend node355 [(3, node98), (6, node52)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower98
  · exact lower52
def entries88 : List Graph := [node352, node353, node354, node355]
theorem entries_count88 : entries88.length = 4 := by decide +kernel
theorem arc_count88 : (entries88.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by decide +kernel
end RawCert
