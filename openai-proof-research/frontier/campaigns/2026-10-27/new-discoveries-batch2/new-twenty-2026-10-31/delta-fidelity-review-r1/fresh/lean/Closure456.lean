import Closure455
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1824 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1824 : ∀ h, Pure node1824 h → 11 ≤ h.length := by
  apply indexed_extend node1824 [(2, node1438), (3, node971), (5, node1148), (8, node1137), (9, node1138), (10, node1139)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1438
  · exact lower971
  · exact lower1148
  · exact lower1137
  · exact lower1138
  · exact lower1139
def node1825 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0]]
theorem lower1825 : ∀ h, Pure node1825 h → 11 ≤ h.length := by
  apply indexed_extend node1825 [(3, node972), (5, node1149), (6, node1153), (8, node1141), (9, node1142), (11, node1140)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower972
  · exact lower1149
  · exact lower1153
  · exact lower1141
  · exact lower1142
  · exact lower1140
def node1826 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1826 : ∀ h, Pure node1826 h → 11 ≤ h.length := by
  apply indexed_extend node1826 [(2, node1439), (5, node1150), (6, node1154), (8, node1143), (9, node1144), (10, node1145), (12, node1140)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1439
  · exact lower1150
  · exact lower1154
  · exact lower1143
  · exact lower1144
  · exact lower1145
  · exact lower1140
def node1827 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2], [1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1827 : ∀ h, Pure node1827 h → 11 ≤ h.length := by
  apply indexed_extend node1827 [(2, node1440), (3, node973), (5, node1152), (9, node1146), (10, node1143), (12, node1141), (14, node1137)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1440
  · exact lower973
  · exact lower1152
  · exact lower1146
  · exact lower1143
  · exact lower1141
  · exact lower1137
def entries456 : List Graph := [node1824, node1825, node1826, node1827]
theorem entries_count456 : entries456.length = 4 := by decide +kernel
theorem arc_count456 : (entries456.map (fun g => ((verts g).filter (wye g)).length)).sum = 26 := by decide +kernel
end RawCert
