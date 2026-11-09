import Closure266
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1068 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower1068 : ∀ h, Pure node1068 h → 11 ≤ h.length := by
  apply indexed_extend node1068 [(2, node519), (4, node674), (8, node370), (9, node371), (11, node344)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower519
  · exact lower674
  · exact lower370
  · exact lower371
  · exact lower344
def node1069 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1069 : ∀ h, Pure node1069 h → 11 ≤ h.length := by
  apply indexed_extend node1069 [(2, node520), (3, node507), (8, node372), (9, node370), (11, node345)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower520
  · exact lower507
  · exact lower372
  · exact lower370
  · exact lower345
def node1070 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1070 : ∀ h, Pure node1070 h → 11 ≤ h.length := by
  apply indexed_extend node1070 [(3, node508), (4, node675), (8, node372), (9, node371)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower508
  · exact lower675
  · exact lower372
  · exact lower371
def node1071 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1071 : ∀ h, Pure node1071 h → 11 ≤ h.length := by
  apply indexed_extend node1071 [(1, node505), (4, node427), (12, node351), (13, node346)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower505
  · exact lower427
  · exact lower351
  · exact lower346
def entries267 : List Graph := [node1068, node1069, node1070, node1071]
theorem entries_count267 : entries267.length = 4 := by decide +kernel
theorem arc_count267 : (entries267.map (fun g => ((verts g).filter (wye g)).length)).sum = 18 := by decide +kernel
end RawCert
