import Closure273
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1096 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1096 : ∀ h, Pure node1096 h → 11 ≤ h.length := by
  apply indexed_extend node1096 [(2, node649), (6, node434), (7, node390), (9, node388), (11, node387)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower649
  · exact lower434
  · exact lower390
  · exact lower388
  · exact lower387
def node1097 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1097 : ∀ h, Pure node1097 h → 11 ≤ h.length := by
  apply indexed_extend node1097 [(7, node391), (9, node388), (13, node385)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower391
  · exact lower388
  · exact lower385
def node1098 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1098 : ∀ h, Pure node1098 h → 11 ≤ h.length := by
  apply indexed_extend node1098 [(2, node650), (6, node443), (8, node391), (9, node390), (11, node389), (13, node386)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower650
  · exact lower443
  · exact lower391
  · exact lower390
  · exact lower389
  · exact lower386
def node1099 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 2, 0, 0, 0]]
theorem lower1099 : ∀ h, Pure node1099 h → 11 ≤ h.length := by
  apply indexed_extend node1099 [(6, node435), (8, node393), (10, node392)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower435
  · exact lower393
  · exact lower392
def entries274 : List Graph := [node1096, node1097, node1098, node1099]
theorem entries_count274 : entries274.length = 4 := by decide +kernel
theorem arc_count274 : (entries274.map (fun g => ((verts g).filter (wye g)).length)).sum = 17 := by decide +kernel
end RawCert
