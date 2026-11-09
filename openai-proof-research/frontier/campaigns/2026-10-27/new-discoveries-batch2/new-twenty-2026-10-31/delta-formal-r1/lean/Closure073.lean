import Closure072
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node292 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0]]
theorem lower292 : ∀ h, Pure node292 h → 11 ≤ h.length := by
  apply indexed_extend node292 [(6, node31)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower31
def node293 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 0, 0]]
theorem lower293 : ∀ h, Pure node293 h → 11 ≤ h.length := by
  apply indexed_extend node293 [(7, node32)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower32
def node294 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower294 : ∀ h, Pure node294 h → 11 ≤ h.length := by
  apply indexed_extend node294 [(6, node33), (12, node27)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower33
  · exact lower27
def node295 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower295 : ∀ h, Pure node295 h → 11 ≤ h.length := by
  apply indexed_extend node295 [(2, node38), (7, node33), (10, node31), (12, node28)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower38
  · exact lower33
  · exact lower31
  · exact lower28
def entries73 : List Graph := [node292, node293, node294, node295]
theorem entries_count73 : entries73.length = 4 := by decide +kernel
theorem arc_count73 : (entries73.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by decide +kernel
end RawCert
