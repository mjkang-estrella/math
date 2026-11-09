import Closure111
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node448 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [0, 1, 2, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0, 0]]
theorem lower448 : ∀ h, Pure node448 h → 11 ≤ h.length := by
  apply indexed_extend node448 [(2, node176), (8, node83), (10, node82)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower176
  · exact lower83
  · exact lower82
def node449 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 0, 1, 0], [1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower449 : ∀ h, Pure node449 h → 11 ≤ h.length := by
  apply indexed_extend node449 [(3, node27), (7, node84)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower27
  · exact lower84
def node450 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower450 : ∀ h, Pure node450 h → 11 ≤ h.length := by
  apply indexed_extend node450 [(2, node177), (3, node28), (8, node84)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower177
  · exact lower28
  · exact lower84
def node451 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 1, 0]]
theorem lower451 : ∀ h, Pure node451 h → 11 ≤ h.length := by
  apply indexed_extend node451 [(7, node85)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower85
def entries112 : List Graph := [node448, node449, node450, node451]
theorem entries_count112 : entries112.length = 4 := by decide +kernel
theorem arc_count112 : (entries112.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by decide +kernel
end RawCert
