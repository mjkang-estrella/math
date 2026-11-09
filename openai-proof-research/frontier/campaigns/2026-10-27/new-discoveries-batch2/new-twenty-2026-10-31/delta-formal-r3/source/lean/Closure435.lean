import Closure434
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1740 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0]]
theorem lower1740 : ∀ h, Pure node1740 h → 11 ≤ h.length := by
  apply indexed_extend node1740 [(3, node956), (6, node968), (8, node954)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower956
  · exact lower968
  · exact lower954
def node1741 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2], [1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower1741 : ∀ h, Pure node1741 h → 11 ≤ h.length := by
  apply indexed_extend node1741 [(3, node966), (6, node957), (8, node959), (9, node960)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower966
  · exact lower957
  · exact lower959
  · exact lower960
def node1742 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower1742 : ∀ h, Pure node1742 h → 11 ≤ h.length := by
  apply indexed_extend node1742 [(6, node958), (7, node961), (8, node962), (9, node963)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower958
  · exact lower961
  · exact lower962
  · exact lower963
def node1743 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1743 : ∀ h, Pure node1743 h → 11 ≤ h.length := by
  apply indexed_extend node1743 [(3, node967), (7, node964), (12, node958), (13, node957)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower967
  · exact lower964
  · exact lower958
  · exact lower957
def entries435 : List Graph := [node1740, node1741, node1742, node1743]
theorem entries_count435 : entries435.length = 4 := by decide +kernel
theorem census_node1740 : ((verts node1740).filter (wye node1740)).length = 3 := by decide +kernel
theorem census_node1741 : ((verts node1741).filter (wye node1741)).length = 4 := by decide +kernel
theorem census_node1742 : ((verts node1742).filter (wye node1742)).length = 4 := by decide +kernel
theorem census_node1743 : ((verts node1743).filter (wye node1743)).length = 4 := by decide +kernel
theorem arc_count435 : (entries435.map (fun g => ((verts g).filter (wye g)).length)).sum = 15 := by
  simp only [entries435, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1740, census_node1741, census_node1742, census_node1743]
  decide +kernel
end RawCert
