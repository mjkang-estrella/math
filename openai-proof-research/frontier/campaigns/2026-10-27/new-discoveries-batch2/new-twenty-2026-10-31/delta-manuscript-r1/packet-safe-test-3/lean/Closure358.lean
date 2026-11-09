import Closure357
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1432 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1432 : ∀ h, Pure node1432 h → 11 ≤ h.length := by
  apply indexed_extend node1432 [(5, node676), (8, node670), (9, node669), (11, node661)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower676
  · exact lower670
  · exact lower669
  · exact lower661
def node1433 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1433 : ∀ h, Pure node1433 h → 11 ≤ h.length := by
  apply indexed_extend node1433 [(5, node676), (6, node677), (9, node671), (11, node663), (13, node662)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower676
  · exact lower677
  · exact lower671
  · exact lower663
  · exact lower662
def node1434 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [1, 0, 1, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1434 : ∀ h, Pure node1434 h → 11 ≤ h.length := by
  apply indexed_extend node1434 [(3, node681), (8, node673), (9, node672), (11, node665), (13, node664)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower681
  · exact lower673
  · exact lower672
  · exact lower665
  · exact lower664
def node1435 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1435 : ∀ h, Pure node1435 h → 11 ≤ h.length := by
  apply indexed_extend node1435 [(3, node682), (8, node675), (9, node674), (11, node666)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower682
  · exact lower675
  · exact lower674
  · exact lower666
def entries358 : List Graph := [node1432, node1433, node1434, node1435]
theorem entries_count358 : entries358.length = 4 := by decide +kernel
theorem census_node1432 : ((verts node1432).filter (wye node1432)).length = 4 := by decide +kernel
theorem census_node1433 : ((verts node1433).filter (wye node1433)).length = 5 := by decide +kernel
theorem census_node1434 : ((verts node1434).filter (wye node1434)).length = 5 := by decide +kernel
theorem census_node1435 : ((verts node1435).filter (wye node1435)).length = 4 := by decide +kernel
theorem arc_count358 : (entries358.map (fun g => ((verts g).filter (wye g)).length)).sum = 18 := by
  simp only [entries358, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1432, census_node1433, census_node1434, census_node1435]
  decide +kernel
end RawCert
