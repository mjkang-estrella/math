import Closure542
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2172 : Graph := [[0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2172 : ∀ h, Pure node2172 h → 11 ≤ h.length := by
  apply indexed_extend node2172 [(1, node1437), (5, node1710), (6, node1711), (7, node1712), (8, node1713), (10, node1709), (13, node1747), (14, node1708)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1437
  · exact lower1710
  · exact lower1711
  · exact lower1712
  · exact lower1713
  · exact lower1709
  · exact lower1747
  · exact lower1708
def node2173 : Graph := [[0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0]]
theorem lower2173 : ∀ h, Pure node2173 h → 11 ≤ h.length := by
  apply indexed_extend node2173 [(3, node1726), (4, node1721), (6, node1723), (8, node1741), (9, node1714), (10, node1715), (11, node1718)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1726
  · exact lower1721
  · exact lower1723
  · exact lower1741
  · exact lower1714
  · exact lower1715
  · exact lower1718
def node2174 : Graph := [[0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower2174 : ∀ h, Pure node2174 h → 11 ≤ h.length := by
  apply indexed_extend node2174 [(4, node1722), (6, node1724), (7, node1725), (8, node1742), (9, node1716), (10, node1717)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1722
  · exact lower1724
  · exact lower1725
  · exact lower1742
  · exact lower1716
  · exact lower1717
def node2175 : Graph := [[0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower2175 : ∀ h, Pure node2175 h → 11 ≤ h.length := by
  apply indexed_extend node2175 [(3, node1734), (4, node1727), (6, node1731), (8, node1745), (10, node1719), (13, node1716), (14, node1714)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1734
  · exact lower1727
  · exact lower1731
  · exact lower1745
  · exact lower1719
  · exact lower1716
  · exact lower1714
def entries543 : List Graph := [node2172, node2173, node2174, node2175]
theorem entries_count543 : entries543.length = 4 := by decide +kernel
theorem arc_count543 : (entries543.map (fun g => ((verts g).filter (wye g)).length)).sum = 28 := by decide +kernel
end RawCert
