import Closure116
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node468 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [2, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower468 : ∀ h, Pure node468 h → 11 ≤ h.length := by
  apply indexed_extend node468 [(0, node261), (3, node41), (11, node119)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower261
  · exact lower41
  · exact lower119
def node469 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 0, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0]]
theorem lower469 : ∀ h, Pure node469 h → 11 ≤ h.length := by
  apply indexed_extend node469 [(0, node263), (5, node101), (8, node89), (11, node120)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower263
  · exact lower101
  · exact lower89
  · exact lower120
def node470 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower470 : ∀ h, Pure node470 h → 11 ≤ h.length := by
  apply indexed_extend node470 [(0, node264), (4, node116), (5, node109), (9, node89)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower264
  · exact lower116
  · exact lower109
  · exact lower89
def node471 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower471 : ∀ h, Pure node471 h → 11 ≤ h.length := by
  apply indexed_extend node471 [(0, node265), (5, node110)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower265
  · exact lower110
def entries117 : List Graph := [node468, node469, node470, node471]
theorem entries_count117 : entries117.length = 4 := by decide +kernel
theorem arc_count117 : (entries117.map (fun g => ((verts g).filter (wye g)).length)).sum = 13 := by decide +kernel
end RawCert
