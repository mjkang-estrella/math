import Closure454
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1820 : Graph := [[0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1820 : ∀ h, Pure node1820 h → 11 ≤ h.length := by
  apply indexed_extend node1820 [(1, node1435), (2, node1432), (4, node1129), (6, node1122), (9, node1120), (10, node1119), (12, node1111), (13, node1115)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1435
  · exact lower1432
  · exact lower1129
  · exact lower1122
  · exact lower1120
  · exact lower1119
  · exact lower1111
  · exact lower1115
def node1821 : Graph := [[0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1821 : ∀ h, Pure node1821 h → 11 ≤ h.length := by
  apply indexed_extend node1821 [(2, node1433), (6, node1122), (7, node1123), (10, node1121), (12, node1113), (13, node1116), (14, node1112)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1433
  · exact lower1122
  · exact lower1123
  · exact lower1121
  · exact lower1113
  · exact lower1116
  · exact lower1112
def node1822 : Graph := [[0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1822 : ∀ h, Pure node1822 h → 11 ≤ h.length := by
  apply indexed_extend node1822 [(1, node1436), (5, node1129), (7, node1128), (9, node1127), (12, node1125), (13, node1126), (14, node1124)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1436
  · exact lower1129
  · exact lower1128
  · exact lower1127
  · exact lower1125
  · exact lower1126
  · exact lower1124
def node1823 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1823 : ∀ h, Pure node1823 h → 11 ≤ h.length := by
  apply indexed_extend node1823 [(2, node1437), (5, node1133), (6, node1134), (7, node1135), (8, node1136), (10, node1132), (12, node1131), (14, node1130)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1437
  · exact lower1133
  · exact lower1134
  · exact lower1135
  · exact lower1136
  · exact lower1132
  · exact lower1131
  · exact lower1130
def entries455 : List Graph := [node1820, node1821, node1822, node1823]
theorem entries_count455 : entries455.length = 4 := by decide +kernel
theorem census_node1820 : ((verts node1820).filter (wye node1820)).length = 8 := by decide +kernel
theorem census_node1821 : ((verts node1821).filter (wye node1821)).length = 7 := by decide +kernel
theorem census_node1822 : ((verts node1822).filter (wye node1822)).length = 7 := by decide +kernel
theorem census_node1823 : ((verts node1823).filter (wye node1823)).length = 8 := by decide +kernel
theorem arc_count455 : (entries455.map (fun g => ((verts g).filter (wye g)).length)).sum = 30 := by
  simp only [entries455, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1820, census_node1821, census_node1822, census_node1823]
  decide +kernel
end RawCert
