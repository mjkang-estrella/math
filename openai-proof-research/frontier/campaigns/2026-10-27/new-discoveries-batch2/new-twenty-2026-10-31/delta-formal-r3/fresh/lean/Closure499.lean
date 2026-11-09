import Closure498
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1996 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0]]
theorem lower1996 : ∀ h, Pure node1996 h → 11 ≤ h.length := by
  apply indexed_extend node1996 [(4, node1382), (6, node1407), (7, node1351), (8, node1352), (10, node1344), (13, node1343), (14, node1342)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1382
  · exact lower1407
  · exact lower1351
  · exact lower1352
  · exact lower1344
  · exact lower1343
  · exact lower1342
def node1997 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower1997 : ∀ h, Pure node1997 h → 11 ≤ h.length := by
  apply indexed_extend node1997 [(2, node1614), (4, node1383), (6, node1410), (11, node1346), (12, node1347), (13, node1351), (14, node1345)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1614
  · exact lower1383
  · exact lower1410
  · exact lower1346
  · exact lower1347
  · exact lower1351
  · exact lower1345
def node1998 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0]]
theorem lower1998 : ∀ h, Pure node1998 h → 11 ≤ h.length := by
  apply indexed_extend node1998 [(2, node1615), (4, node1384), (6, node1411), (9, node1350), (11, node1348), (12, node1349), (13, node1352)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1615
  · exact lower1384
  · exact lower1411
  · exact lower1350
  · exact lower1348
  · exact lower1349
  · exact lower1352
def node1999 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 1, 0], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower1999 : ∀ h, Pure node1999 h → 11 ≤ h.length := by
  apply indexed_extend node1999 [(1, node1616), (4, node1412), (5, node1391), (6, node1365), (10, node1353), (11, node1354), (14, node1359)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1616
  · exact lower1412
  · exact lower1391
  · exact lower1365
  · exact lower1353
  · exact lower1354
  · exact lower1359
def entries499 : List Graph := [node1996, node1997, node1998, node1999]
theorem entries_count499 : entries499.length = 4 := by decide +kernel
theorem census_node1996 : ((verts node1996).filter (wye node1996)).length = 7 := by decide +kernel
theorem census_node1997 : ((verts node1997).filter (wye node1997)).length = 7 := by decide +kernel
theorem census_node1998 : ((verts node1998).filter (wye node1998)).length = 7 := by decide +kernel
theorem census_node1999 : ((verts node1999).filter (wye node1999)).length = 7 := by decide +kernel
theorem arc_count499 : (entries499.map (fun g => ((verts g).filter (wye g)).length)).sum = 28 := by
  simp only [entries499, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1996, census_node1997, census_node1998, census_node1999]
  decide +kernel
end RawCert
