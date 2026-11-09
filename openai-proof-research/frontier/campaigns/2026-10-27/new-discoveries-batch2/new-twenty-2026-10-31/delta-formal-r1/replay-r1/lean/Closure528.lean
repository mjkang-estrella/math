import Closure527
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2112 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower2112 : ∀ h, Pure node2112 h → 11 ≤ h.length := by
  apply indexed_extend node2112 [(3, node1621), (5, node1634), (6, node1595), (7, node1598), (8, node1603), (10, node1583), (11, node1585), (12, node1582)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1621
  · exact lower1634
  · exact lower1595
  · exact lower1598
  · exact lower1603
  · exact lower1583
  · exact lower1585
  · exact lower1582
def node2113 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower2113 : ∀ h, Pure node2113 h → 11 ≤ h.length := by
  apply indexed_extend node2113 [(5, node1635), (6, node1596), (7, node1599), (8, node1604), (10, node1584), (12, node1582)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1635
  · exact lower1596
  · exact lower1599
  · exact lower1604
  · exact lower1584
  · exact lower1582
def node2114 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower2114 : ∀ h, Pure node2114 h → 11 ≤ h.length := by
  apply indexed_extend node2114 [(3, node1622), (7, node1600), (8, node1605), (10, node1586), (11, node1583), (12, node1584), (14, node1580)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1622
  · exact lower1600
  · exact lower1605
  · exact lower1586
  · exact lower1583
  · exact lower1584
  · exact lower1580
def node2115 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower2115 : ∀ h, Pure node2115 h → 11 ≤ h.length := by
  apply indexed_extend node2115 [(5, node1636), (6, node1597), (7, node1601), (10, node1586), (11, node1585), (14, node1581)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1636
  · exact lower1597
  · exact lower1601
  · exact lower1586
  · exact lower1585
  · exact lower1581
def entries528 : List Graph := [node2112, node2113, node2114, node2115]
theorem entries_count528 : entries528.length = 4 := by decide +kernel
theorem arc_count528 : (entries528.map (fun g => ((verts g).filter (wye g)).length)).sum = 27 := by decide +kernel
end RawCert
