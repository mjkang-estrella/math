import Closure343
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1376 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1376 : ∀ h, Pure node1376 h → 11 ≤ h.length := by
  apply indexed_extend node1376 [(2, node844), (6, node600), (7, node601), (9, node588)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower844
  · exact lower600
  · exact lower601
  · exact lower588
def node1377 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0]]
theorem lower1377 : ∀ h, Pure node1377 h → 11 ≤ h.length := by
  apply indexed_extend node1377 [(2, node845), (7, node602), (10, node588), (12, node598), (13, node587)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower845
  · exact lower602
  · exact lower588
  · exact lower598
  · exact lower587
def node1378 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0]]
theorem lower1378 : ∀ h, Pure node1378 h → 11 ≤ h.length := by
  apply indexed_extend node1378 [(4, node642), (5, node633), (10, node593), (12, node590), (13, node589)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower642
  · exact lower633
  · exact lower593
  · exact lower590
  · exact lower589
def node1379 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 2, 0]]
theorem lower1379 : ∀ h, Pure node1379 h → 11 ≤ h.length := by
  apply indexed_extend node1379 [(4, node643), (5, node634), (9, node594), (10, node595), (12, node591)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower643
  · exact lower634
  · exact lower594
  · exact lower595
  · exact lower591
def entries344 : List Graph := [node1376, node1377, node1378, node1379]
theorem entries_count344 : entries344.length = 4 := by decide +kernel
theorem census_node1376 : ((verts node1376).filter (wye node1376)).length = 4 := by decide +kernel
theorem census_node1377 : ((verts node1377).filter (wye node1377)).length = 5 := by decide +kernel
theorem census_node1378 : ((verts node1378).filter (wye node1378)).length = 5 := by decide +kernel
theorem census_node1379 : ((verts node1379).filter (wye node1379)).length = 5 := by decide +kernel
theorem arc_count344 : (entries344.map (fun g => ((verts g).filter (wye g)).length)).sum = 19 := by
  simp only [entries344, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1376, census_node1377, census_node1378, census_node1379]
  decide +kernel
end RawCert
