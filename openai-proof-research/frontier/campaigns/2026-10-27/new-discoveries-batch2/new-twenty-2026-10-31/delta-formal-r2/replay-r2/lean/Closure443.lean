import Closure442
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1772 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1772 : ∀ h, Pure node1772 h → 11 ≤ h.length := by
  apply indexed_extend node1772 [(1, node1070), (2, node1058), (4, node1076), (5, node1120), (9, node1010), (10, node1009), (13, node1002)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1070
  · exact lower1058
  · exact lower1076
  · exact lower1120
  · exact lower1010
  · exact lower1009
  · exact lower1002
def node1773 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1773 : ∀ h, Pure node1773 h → 11 ≤ h.length := by
  apply indexed_extend node1773 [(2, node1059), (3, node1079), (5, node1121), (7, node1011), (8, node1012), (9, node1013), (12, node993)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1059
  · exact lower1079
  · exact lower1121
  · exact lower1011
  · exact lower1012
  · exact lower1013
  · exact lower993
def node1774 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1774 : ∀ h, Pure node1774 h → 11 ≤ h.length := by
  apply indexed_extend node1774 [(2, node1060), (3, node1080), (5, node1122), (8, node1014), (10, node1011), (12, node996), (13, node1003)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1060
  · exact lower1080
  · exact lower1122
  · exact lower1014
  · exact lower1011
  · exact lower996
  · exact lower1003
def node1775 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 2], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1775 : ∀ h, Pure node1775 h → 11 ≤ h.length := by
  apply indexed_extend node1775 [(2, node1061), (3, node1081), (5, node1123), (10, node1012), (12, node997), (13, node1004), (14, node994)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1061
  · exact lower1081
  · exact lower1123
  · exact lower1012
  · exact lower997
  · exact lower1004
  · exact lower994
def entries443 : List Graph := [node1772, node1773, node1774, node1775]
theorem entries_count443 : entries443.length = 4 := by decide +kernel
theorem arc_count443 : (entries443.map (fun g => ((verts g).filter (wye g)).length)).sum = 28 := by decide +kernel
end RawCert
