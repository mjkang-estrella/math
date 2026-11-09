import Closure369
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1480 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1480 : ∀ h, Pure node1480 h → 11 ≤ h.length := by
  apply indexed_extend node1480 [(0, node434), (3, node732), (5, node781), (7, node713), (10, node820), (11, node701)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower434
  · exact lower732
  · exact lower781
  · exact lower713
  · exact lower820
  · exact lower701
def node1481 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 2, 1, 0]]
theorem lower1481 : ∀ h, Pure node1481 h → 11 ≤ h.length := by
  apply indexed_extend node1481 [(0, node438), (2, node364), (3, node733), (5, node782), (8, node714), (10, node822), (11, node702)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower438
  · exact lower364
  · exact lower733
  · exact lower782
  · exact lower714
  · exact lower822
  · exact lower702
def node1482 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 2], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1482 : ∀ h, Pure node1482 h → 11 ≤ h.length := by
  apply indexed_extend node1482 [(0, node439), (2, node365), (3, node734), (5, node783), (6, node713), (11, node703)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower439
  · exact lower365
  · exact lower734
  · exact lower783
  · exact lower713
  · exact lower703
def node1483 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1483 : ∀ h, Pure node1483 h → 11 ≤ h.length := by
  apply indexed_extend node1483 [(0, node440), (2, node366), (3, node735), (7, node714), (10, node809), (11, node704)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower440
  · exact lower366
  · exact lower735
  · exact lower714
  · exact lower809
  · exact lower704
def entries370 : List Graph := [node1480, node1481, node1482, node1483]
theorem entries_count370 : entries370.length = 4 := by decide +kernel
theorem census_node1480 : ((verts node1480).filter (wye node1480)).length = 6 := by decide +kernel
theorem census_node1481 : ((verts node1481).filter (wye node1481)).length = 7 := by decide +kernel
theorem census_node1482 : ((verts node1482).filter (wye node1482)).length = 6 := by decide +kernel
theorem census_node1483 : ((verts node1483).filter (wye node1483)).length = 6 := by decide +kernel
theorem arc_count370 : (entries370.map (fun g => ((verts g).filter (wye g)).length)).sum = 25 := by
  simp only [entries370, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1480, census_node1481, census_node1482, census_node1483]
  decide +kernel
end RawCert
