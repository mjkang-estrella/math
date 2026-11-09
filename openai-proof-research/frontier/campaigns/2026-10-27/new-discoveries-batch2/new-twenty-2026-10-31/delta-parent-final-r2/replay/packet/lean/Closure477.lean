import Closure476
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1908 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1908 : ∀ h, Pure node1908 h → 11 ≤ h.length := by
  apply indexed_extend node1908 [(0, node1747), (3, node1050), (6, node1218), (7, node1219), (8, node1220), (9, node1221), (12, node1382), (14, node1199)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1747
  · exact lower1050
  · exact lower1218
  · exact lower1219
  · exact lower1220
  · exact lower1221
  · exact lower1382
  · exact lower1199
def node1909 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1909 : ∀ h, Pure node1909 h → 11 ≤ h.length := by
  apply indexed_extend node1909 [(0, node1663), (1, node1509), (3, node1071), (5, node1297), (6, node1222), (13, node1210), (14, node1200)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1663
  · exact lower1509
  · exact lower1071
  · exact lower1297
  · exact lower1222
  · exact lower1210
  · exact lower1200
def node1910 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1910 : ∀ h, Pure node1910 h → 11 ≤ h.length := by
  apply indexed_extend node1910 [(0, node1664), (1, node1510), (3, node1072), (7, node1223), (11, node1357), (13, node1211), (14, node1201)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1664
  · exact lower1510
  · exact lower1072
  · exact lower1223
  · exact lower1357
  · exact lower1211
  · exact lower1201
def node1911 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1911 : ∀ h, Pure node1911 h → 11 ≤ h.length := by
  apply indexed_extend node1911 [(0, node1675), (1, node1526), (2, node1515), (3, node1073), (6, node1224), (8, node1228)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1675
  · exact lower1526
  · exact lower1515
  · exact lower1073
  · exact lower1224
  · exact lower1228
def entries477 : List Graph := [node1908, node1909, node1910, node1911]
theorem entries_count477 : entries477.length = 4 := by decide +kernel
theorem census_node1908 : ((verts node1908).filter (wye node1908)).length = 8 := by decide +kernel
theorem census_node1909 : ((verts node1909).filter (wye node1909)).length = 7 := by decide +kernel
theorem census_node1910 : ((verts node1910).filter (wye node1910)).length = 7 := by decide +kernel
theorem census_node1911 : ((verts node1911).filter (wye node1911)).length = 6 := by decide +kernel
theorem arc_count477 : (entries477.map (fun g => ((verts g).filter (wye g)).length)).sum = 28 := by
  simp only [entries477, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1908, census_node1909, census_node1910, census_node1911]
  decide +kernel
end RawCert
