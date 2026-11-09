import Closure044
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node180 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 2], [0, 0, 1, 0, 0, 2, 2, 0, 0, 1, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0]]
theorem lower180 : ∀ h, Pure node180 h → 11 ≤ h.length := by
  apply indexed_extend node180 [(0, node4), (5, node16)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower4
  · exact lower16
def node181 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 1], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0]]
theorem lower181 : ∀ h, Pure node181 h → 11 ≤ h.length := by
  apply indexed_extend node181 [(0, node5), (2, node2), (9, node17)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower5
  · exact lower2
  · exact lower17
def node182 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0], [0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower182 : ∀ h, Pure node182 h → 11 ≤ h.length := by
  apply indexed_extend node182 [(0, node0), (4, node15)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower0
  · exact lower15
def node183 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3], [2, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 3, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower183 : ∀ h, Pure node183 h → 11 ≤ h.length := by
  apply indexed_extend node183 [(0, node12)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower12
def entries45 : List Graph := [node180, node181, node182, node183]
theorem entries_count45 : entries45.length = 4 := by decide +kernel
theorem arc_count45 : (entries45.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by decide +kernel
end RawCert
