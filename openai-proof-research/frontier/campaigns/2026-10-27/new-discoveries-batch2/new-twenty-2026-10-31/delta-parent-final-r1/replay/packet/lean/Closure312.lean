import Closure311
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1248 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1248 : ∀ h, Pure node1248 h → 11 ≤ h.length := by
  apply indexed_extend node1248 [(5, node519), (7, node517), (8, node518)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower519
  · exact lower517
  · exact lower518
def node1249 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1249 : ∀ h, Pure node1249 h → 11 ≤ h.length := by
  apply indexed_extend node1249 [(2, node741), (9, node517), (13, node495)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower741
  · exact lower517
  · exact lower495
def node1250 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1250 : ∀ h, Pure node1250 h → 11 ≤ h.length := by
  apply indexed_extend node1250 [(2, node742), (5, node520), (9, node518), (13, node496)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower742
  · exact lower520
  · exact lower518
  · exact lower496
def node1251 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1251 : ∀ h, Pure node1251 h → 11 ≤ h.length := by
  apply indexed_extend node1251 [(1, node741), (12, node499), (13, node497)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower741
  · exact lower499
  · exact lower497
def entries312 : List Graph := [node1248, node1249, node1250, node1251]
theorem entries_count312 : entries312.length = 4 := by decide +kernel
theorem arc_count312 : (entries312.map (fun g => ((verts g).filter (wye g)).length)).sum = 13 := by decide +kernel
end RawCert
