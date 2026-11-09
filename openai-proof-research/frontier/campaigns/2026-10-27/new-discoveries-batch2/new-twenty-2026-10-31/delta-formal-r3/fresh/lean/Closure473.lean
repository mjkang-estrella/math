import Closure472
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1892 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower1892 : ∀ h, Pure node1892 h → 11 ≤ h.length := by
  apply indexed_extend node1892 [(0, node1661), (1, node1497), (3, node1039), (5, node1280), (6, node1205), (13, node1190)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1661
  · exact lower1497
  · exact lower1039
  · exact lower1280
  · exact lower1205
  · exact lower1190
def node1893 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower1893 : ∀ h, Pure node1893 h → 11 ≤ h.length := by
  apply indexed_extend node1893 [(0, node1662), (1, node1498), (3, node1040), (7, node1206), (12, node1356), (13, node1191)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1662
  · exact lower1498
  · exact lower1040
  · exact lower1206
  · exact lower1356
  · exact lower1191
def node1894 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1894 : ∀ h, Pure node1894 h → 11 ≤ h.length := by
  apply indexed_extend node1894 [(0, node1677), (1, node1499), (4, node1310), (5, node1282), (8, node1203), (10, node1202), (12, node1365), (14, node1195)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1677
  · exact lower1499
  · exact lower1310
  · exact lower1282
  · exact lower1203
  · exact lower1202
  · exact lower1365
  · exact lower1195
def node1895 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1895 : ∀ h, Pure node1895 h → 11 ≤ h.length := by
  apply indexed_extend node1895 [(0, node1679), (1, node1508), (2, node1504), (4, node1310), (7, node1207), (8, node1204), (12, node1366), (14, node1198)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1679
  · exact lower1508
  · exact lower1504
  · exact lower1310
  · exact lower1207
  · exact lower1204
  · exact lower1366
  · exact lower1198
def entries473 : List Graph := [node1892, node1893, node1894, node1895]
theorem entries_count473 : entries473.length = 4 := by decide +kernel
theorem census_node1892 : ((verts node1892).filter (wye node1892)).length = 6 := by decide +kernel
theorem census_node1893 : ((verts node1893).filter (wye node1893)).length = 6 := by decide +kernel
theorem census_node1894 : ((verts node1894).filter (wye node1894)).length = 8 := by decide +kernel
theorem census_node1895 : ((verts node1895).filter (wye node1895)).length = 8 := by decide +kernel
theorem arc_count473 : (entries473.map (fun g => ((verts g).filter (wye g)).length)).sum = 28 := by
  simp only [entries473, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1892, census_node1893, census_node1894, census_node1895]
  decide +kernel
end RawCert
