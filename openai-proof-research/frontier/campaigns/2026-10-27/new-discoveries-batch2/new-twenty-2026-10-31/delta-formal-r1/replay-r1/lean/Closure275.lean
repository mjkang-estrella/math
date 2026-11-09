import Closure274
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1100 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower1100 : ∀ h, Pure node1100 h → 11 ≤ h.length := by
  apply indexed_extend node1100 [(2, node651), (6, node438), (8, node394), (9, node395), (11, node392)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower651
  · exact lower438
  · exact lower394
  · exact lower395
  · exact lower392
def node1101 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1101 : ∀ h, Pure node1101 h → 11 ≤ h.length := by
  apply indexed_extend node1101 [(2, node652), (6, node448), (8, node396), (9, node394), (11, node393)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower652
  · exact lower448
  · exact lower396
  · exact lower394
  · exact lower393
def node1102 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1102 : ∀ h, Pure node1102 h → 11 ≤ h.length := by
  apply indexed_extend node1102 [(8, node396), (9, node395)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower396
  · exact lower395
def node1103 : Graph := [[0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0]]
theorem lower1103 : ∀ h, Pure node1103 h → 11 ≤ h.length := by
  apply indexed_extend node1103 [(4, node418), (7, node401), (8, node398), (10, node397)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower418
  · exact lower401
  · exact lower398
  · exact lower397
def entries275 : List Graph := [node1100, node1101, node1102, node1103]
theorem entries_count275 : entries275.length = 4 := by decide +kernel
theorem arc_count275 : (entries275.map (fun g => ((verts g).filter (wye g)).length)).sum = 16 := by decide +kernel
end RawCert
