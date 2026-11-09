import Closure382
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1532 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1532 : ∀ h, Pure node1532 h → 11 ≤ h.length := by
  apply indexed_extend node1532 [(4, node743), (6, node741), (7, node742), (13, node740)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower743
  · exact lower741
  · exact lower742
  · exact lower740
def node1533 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1533 : ∀ h, Pure node1533 h → 11 ≤ h.length := by
  apply indexed_extend node1533 [(2, node653), (5, node747), (8, node745), (11, node852)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower653
  · exact lower747
  · exact lower745
  · exact lower852
def node1534 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 1, 0]]
theorem lower1534 : ∀ h, Pure node1534 h → 11 ≤ h.length := by
  apply indexed_extend node1534 [(2, node654), (5, node748), (6, node749), (7, node750), (8, node746), (11, node853)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower654
  · exact lower748
  · exact lower749
  · exact lower750
  · exact lower746
  · exact lower853
def node1535 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower1535 : ∀ h, Pure node1535 h → 11 ≤ h.length := by
  apply indexed_extend node1535 [(2, node655), (4, node744), (5, node753), (8, node751), (11, node855)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower655
  · exact lower744
  · exact lower753
  · exact lower751
  · exact lower855
def entries383 : List Graph := [node1532, node1533, node1534, node1535]
theorem entries_count383 : entries383.length = 4 := by decide +kernel
theorem census_node1532 : ((verts node1532).filter (wye node1532)).length = 4 := by decide +kernel
theorem census_node1533 : ((verts node1533).filter (wye node1533)).length = 4 := by decide +kernel
theorem census_node1534 : ((verts node1534).filter (wye node1534)).length = 6 := by decide +kernel
theorem census_node1535 : ((verts node1535).filter (wye node1535)).length = 5 := by decide +kernel
theorem arc_count383 : (entries383.map (fun g => ((verts g).filter (wye g)).length)).sum = 19 := by
  simp only [entries383, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1532, census_node1533, census_node1534, census_node1535]
  decide +kernel
end RawCert
