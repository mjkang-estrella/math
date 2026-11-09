import Closure535
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2144 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower2144 : ∀ h, Pure node2144 h → 11 ≤ h.length := by
  apply indexed_extend node2144 [(0, node1438), (1, node1417), (3, node1678), (5, node1679), (7, node1708), (8, node1659), (9, node1660), (14, node1726)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1438
  · exact lower1417
  · exact lower1678
  · exact lower1679
  · exact lower1708
  · exact lower1659
  · exact lower1660
  · exact lower1726
def node2145 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0]]
theorem lower2145 : ∀ h, Pure node2145 h → 11 ≤ h.length := by
  apply indexed_extend node2145 [(0, node972), (5, node1680), (6, node1681), (8, node1661), (9, node1662), (13, node1722)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower972
  · exact lower1680
  · exact lower1681
  · exact lower1661
  · exact lower1662
  · exact lower1722
def node2146 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2146 : ∀ h, Pure node2146 h → 11 ≤ h.length := by
  apply indexed_extend node2146 [(0, node973), (3, node1686), (5, node1683), (9, node1663), (12, node1661), (13, node1727), (14, node1654)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower973
  · exact lower1686
  · exact lower1683
  · exact lower1663
  · exact lower1661
  · exact lower1727
  · exact lower1654
def node2147 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2147 : ∀ h, Pure node2147 h → 11 ≤ h.length := by
  apply indexed_extend node2147 [(0, node974), (3, node1687), (6, node1684), (9, node1664), (12, node1662), (13, node1728), (14, node1655)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower974
  · exact lower1687
  · exact lower1684
  · exact lower1664
  · exact lower1662
  · exact lower1728
  · exact lower1655
def entries536 : List Graph := [node2144, node2145, node2146, node2147]
theorem entries_count536 : entries536.length = 4 := by decide +kernel
theorem arc_count536 : (entries536.map (fun g => ((verts g).filter (wye g)).length)).sum = 28 := by decide +kernel
end RawCert
