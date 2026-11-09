import Closure146
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node588 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [2, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 1, 0]]
theorem lower588 : ∀ h, Pure node588 h → 11 ≤ h.length := by
  apply indexed_extend node588 [(2, node222), (7, node124)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower222
  · exact lower124
def node589 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower589 : ∀ h, Pure node589 h → 11 ≤ h.length := by
  apply indexed_extend node589 [(4, node141), (5, node132), (10, node120)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower141
  · exact lower132
  · exact lower120
def node590 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0]]
theorem lower590 : ∀ h, Pure node590 h → 11 ≤ h.length := by
  apply indexed_extend node590 [(5, node133)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower133
def node591 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0]]
theorem lower591 : ∀ h, Pure node591 h → 11 ≤ h.length := by
  apply indexed_extend node591 [(5, node134), (9, node121)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower134
  · exact lower121
def entries147 : List Graph := [node588, node589, node590, node591]
theorem entries_count147 : entries147.length = 4 := by decide +kernel
theorem arc_count147 : (entries147.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by decide +kernel
end RawCert
