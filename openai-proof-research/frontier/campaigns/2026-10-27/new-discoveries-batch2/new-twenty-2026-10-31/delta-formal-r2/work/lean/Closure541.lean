import Closure540
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2164 : Graph := [[0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower2164 : ∀ h, Pure node2164 h → 11 ≤ h.length := by
  apply indexed_extend node2164 [(0, node1443), (1, node1422), (3, node1693), (6, node1711), (8, node1691), (10, node1690), (13, node1740)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1443
  · exact lower1422
  · exact lower1693
  · exact lower1711
  · exact lower1691
  · exact lower1690
  · exact lower1740
def node2165 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower2165 : ∀ h, Pure node2165 h → 11 ≤ h.length := by
  apply indexed_extend node2165 [(1, node1130), (3, node1708), (6, node1695), (8, node1696), (9, node1697), (14, node1741)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1130
  · exact lower1708
  · exact lower1695
  · exact lower1696
  · exact lower1697
  · exact lower1741
def node2166 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower2166 : ∀ h, Pure node2166 h → 11 ≤ h.length := by
  apply indexed_extend node2166 [(1, node1131), (6, node1698), (7, node1700), (8, node1701), (9, node1702), (11, node1694), (13, node1742)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1131
  · exact lower1698
  · exact lower1700
  · exact lower1701
  · exact lower1702
  · exact lower1694
  · exact lower1742
def node2167 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower2167 : ∀ h, Pure node2167 h → 11 ≤ h.length := by
  apply indexed_extend node2167 [(1, node1132), (3, node1709), (6, node1699), (7, node1703), (8, node1704), (9, node1705), (12, node1694)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1132
  · exact lower1709
  · exact lower1699
  · exact lower1703
  · exact lower1704
  · exact lower1705
  · exact lower1694
def entries541 : List Graph := [node2164, node2165, node2166, node2167]
theorem entries_count541 : entries541.length = 4 := by decide +kernel
theorem arc_count541 : (entries541.map (fun g => ((verts g).filter (wye g)).length)).sum = 27 := by decide +kernel
end RawCert
