import Closure327
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1312 : Graph := [[0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0], [0, 0, 0, 2, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1312 : ∀ h, Pure node1312 h → 11 ≤ h.length := by
  apply indexed_extend node1312 [(0, node952), (3, node500), (6, node559), (11, node639), (13, node555)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower952
  · exact lower500
  · exact lower559
  · exact lower639
  · exact lower555
def node1313 : Graph := [[0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1313 : ∀ h, Pure node1313 h → 11 ≤ h.length := by
  apply indexed_extend node1313 [(0, node955), (7, node558), (11, node642), (13, node556)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower955
  · exact lower558
  · exact lower642
  · exact lower556
def node1314 : Graph := [[0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0]]
theorem lower1314 : ∀ h, Pure node1314 h → 11 ≤ h.length := by
  apply indexed_extend node1314 [(0, node956), (3, node501), (8, node559), (11, node643)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower956
  · exact lower501
  · exact lower559
  · exact lower643
def node1315 : Graph := [[0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1315 : ∀ h, Pure node1315 h → 11 ≤ h.length := by
  apply indexed_extend node1315 [(0, node905), (1, node791), (12, node558), (13, node557)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower905
  · exact lower791
  · exact lower558
  · exact lower557
def entries328 : List Graph := [node1312, node1313, node1314, node1315]
theorem entries_count328 : entries328.length = 4 := by decide +kernel
theorem arc_count328 : (entries328.map (fun g => ((verts g).filter (wye g)).length)).sum = 17 := by decide +kernel
end RawCert
