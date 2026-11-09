import Closure175
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node704 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 1, 0, 1, 0]]
theorem lower704 : ∀ h, Pure node704 h → 11 ≤ h.length := by
  apply indexed_extend node704 [(0, node78), (2, node48), (7, node181), (10, node209)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower78
  · exact lower48
  · exact lower181
  · exact lower209
def node705 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3], [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower705 : ∀ h, Pure node705 h → 11 ≤ h.length := by
  apply indexed_extend node705 [(0, node79), (3, node183), (5, node202)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower79
  · exact lower183
  · exact lower202
def node706 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0]]
theorem lower706 : ∀ h, Pure node706 h → 11 ≤ h.length := by
  apply indexed_extend node706 [(0, node80), (5, node203), (9, node180)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower80
  · exact lower203
  · exact lower180
def node707 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1, 1, 1, 2, 0, 0, 0]]
theorem lower707 : ∀ h, Pure node707 h → 11 ≤ h.length := by
  apply indexed_extend node707 [(0, node82), (2, node49), (9, node181), (10, node215)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower82
  · exact lower49
  · exact lower181
  · exact lower215
def entries176 : List Graph := [node704, node705, node706, node707]
theorem entries_count176 : entries176.length = 4 := by decide +kernel
theorem arc_count176 : (entries176.map (fun g => ((verts g).filter (wye g)).length)).sum = 14 := by decide +kernel
end RawCert
