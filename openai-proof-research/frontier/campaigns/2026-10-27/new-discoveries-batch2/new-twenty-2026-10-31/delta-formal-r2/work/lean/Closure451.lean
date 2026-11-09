import Closure450
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1804 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1804 : ∀ h, Pure node1804 h → 11 ≤ h.length := by
  apply indexed_extend node1804 [(1, node1253), (2, node1246), (3, node1254), (6, node1080), (8, node1078), (10, node1077), (13, node1049)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1253
  · exact lower1246
  · exact lower1254
  · exact lower1080
  · exact lower1078
  · exact lower1077
  · exact lower1049
def node1805 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1805 : ∀ h, Pure node1805 h → 11 ≤ h.length := by
  apply indexed_extend node1805 [(2, node1247), (6, node1080), (7, node1081), (8, node1082), (10, node1079), (13, node1050), (14, node1042)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1247
  · exact lower1080
  · exact lower1081
  · exact lower1082
  · exact lower1079
  · exact lower1050
  · exact lower1042
def node1806 : Graph := [[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1806 : ∀ h, Pure node1806 h → 11 ≤ h.length := by
  apply indexed_extend node1806 [(2, node1417), (5, node1094), (7, node1130), (8, node1083), (9, node1084), (10, node1085)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1417
  · exact lower1094
  · exact lower1130
  · exact lower1083
  · exact lower1084
  · exact lower1085
def node1807 : Graph := [[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0]]
theorem lower1807 : ∀ h, Pure node1807 h → 11 ≤ h.length := by
  apply indexed_extend node1807 [(5, node1095), (6, node1099), (7, node1131), (8, node1087), (9, node1088), (11, node1086)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1095
  · exact lower1099
  · exact lower1131
  · exact lower1087
  · exact lower1088
  · exact lower1086
def entries451 : List Graph := [node1804, node1805, node1806, node1807]
theorem entries_count451 : entries451.length = 4 := by decide +kernel
theorem arc_count451 : (entries451.map (fun g => ((verts g).filter (wye g)).length)).sum = 26 := by decide +kernel
end RawCert
