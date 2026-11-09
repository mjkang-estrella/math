import Closure493
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1976 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1976 : ∀ h, Pure node1976 h → 11 ≤ h.length := by
  apply indexed_extend node1976 [(1, node1592), (2, node1585), (6, node1387), (7, node1326), (8, node1330), (11, node1319)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1592
  · exact lower1585
  · exact lower1387
  · exact lower1326
  · exact lower1330
  · exact lower1319
def node1977 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0]]
theorem lower1977 : ∀ h, Pure node1977 h → 11 ≤ h.length := by
  apply indexed_extend node1977 [(1, node1593), (2, node1586), (5, node1357), (8, node1331), (11, node1319), (13, node1323), (14, node1317)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1593
  · exact lower1586
  · exact lower1357
  · exact lower1331
  · exact lower1319
  · exact lower1323
  · exact lower1317
def node1978 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower1978 : ∀ h, Pure node1978 h → 11 ≤ h.length := by
  apply indexed_extend node1978 [(4, node1361), (5, node1359), (6, node1388), (7, node1336), (9, node1342), (11, node1320), (12, node1322)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1361
  · exact lower1359
  · exact lower1388
  · exact lower1336
  · exact lower1342
  · exact lower1320
  · exact lower1322
def node1979 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 1], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0]]
theorem lower1979 : ∀ h, Pure node1979 h → 11 ≤ h.length := by
  apply indexed_extend node1979 [(5, node1360), (6, node1389), (7, node1337), (8, node1338), (9, node1343), (11, node1321)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1360
  · exact lower1389
  · exact lower1337
  · exact lower1338
  · exact lower1343
  · exact lower1321
def entries494 : List Graph := [node1976, node1977, node1978, node1979]
theorem entries_count494 : entries494.length = 4 := by decide +kernel
theorem census_node1976 : ((verts node1976).filter (wye node1976)).length = 6 := by decide +kernel
theorem census_node1977 : ((verts node1977).filter (wye node1977)).length = 7 := by decide +kernel
theorem census_node1978 : ((verts node1978).filter (wye node1978)).length = 7 := by decide +kernel
theorem census_node1979 : ((verts node1979).filter (wye node1979)).length = 6 := by decide +kernel
theorem arc_count494 : (entries494.map (fun g => ((verts g).filter (wye g)).length)).sum = 26 := by
  simp only [entries494, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1976, census_node1977, census_node1978, census_node1979]
  decide +kernel
end RawCert
