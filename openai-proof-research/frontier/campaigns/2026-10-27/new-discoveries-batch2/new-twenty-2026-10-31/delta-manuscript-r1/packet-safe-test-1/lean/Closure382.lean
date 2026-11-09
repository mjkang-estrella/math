import Closure381
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1528 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1528 : ∀ h, Pure node1528 h → 11 ≤ h.length := by
  apply indexed_extend node1528 [(0, node694), (7, node738), (10, node847)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower694
  · exact lower738
  · exact lower847
def node1529 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1529 : ∀ h, Pure node1529 h → 11 ≤ h.length := by
  apply indexed_extend node1529 [(0, node695), (3, node791), (9, node738), (13, node727)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower695
  · exact lower791
  · exact lower738
  · exact lower727
def node1530 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower1530 : ∀ h, Pure node1530 h → 11 ≤ h.length := by
  apply indexed_extend node1530 [(0, node696), (2, node519), (8, node739), (10, node848)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower696
  · exact lower519
  · exact lower739
  · exact lower848
def node1531 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1531 : ∀ h, Pure node1531 h → 11 ≤ h.length := by
  apply indexed_extend node1531 [(0, node697), (2, node520), (3, node792), (9, node739), (10, node849)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower697
  · exact lower520
  · exact lower792
  · exact lower739
  · exact lower849
def entries382 : List Graph := [node1528, node1529, node1530, node1531]
theorem entries_count382 : entries382.length = 4 := by decide +kernel
theorem census_node1528 : ((verts node1528).filter (wye node1528)).length = 3 := by decide +kernel
theorem census_node1529 : ((verts node1529).filter (wye node1529)).length = 4 := by decide +kernel
theorem census_node1530 : ((verts node1530).filter (wye node1530)).length = 4 := by decide +kernel
theorem census_node1531 : ((verts node1531).filter (wye node1531)).length = 5 := by decide +kernel
theorem arc_count382 : (entries382.map (fun g => ((verts g).filter (wye g)).length)).sum = 16 := by
  simp only [entries382, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1528, census_node1529, census_node1530, census_node1531]
  decide +kernel
end RawCert
