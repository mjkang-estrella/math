import Closure220
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node884 : Graph := [[0, 0, 3, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0]]
theorem lower884 : ∀ h, Pure node884 h → 11 ≤ h.length := by
  apply indexed_extend node884 [(12, node251)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower251
def node885 : Graph := [[0, 0, 3, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [1, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 2, 0, 0]]
theorem lower885 : ∀ h, Pure node885 h → 11 ≤ h.length := by
  apply indexed_extend node885 [(7, node252)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower252
def node886 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower886 : ∀ h, Pure node886 h → 11 ≤ h.length := by
  apply indexed_extend node886 [(0, node25), (5, node253), (12, node260)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower25
  · exact lower253
  · exact lower260
def node887 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 1, 2, 0, 1, 0, 0, 1, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 0], [2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower887 : ∀ h, Pure node887 h → 11 ≤ h.length := by
  apply indexed_extend node887 [(0, node26), (12, node261)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower26
  · exact lower261
def entries221 : List Graph := [node884, node885, node886, node887]
theorem entries_count221 : entries221.length = 4 := by decide +kernel
theorem arc_count221 : (entries221.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by decide +kernel
end RawCert
