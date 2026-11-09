import Closure499
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node2000 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 1, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower2000 : ∀ h, Pure node2000 h → 11 ≤ h.length := by
  apply indexed_extend node2000 [(1, node1623), (2, node1620), (4, node1412), (6, node1366), (8, node1375), (10, node1355), (14, node1361)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1623
  · exact lower1620
  · exact lower1412
  · exact lower1366
  · exact lower1375
  · exact lower1355
  · exact lower1361
def node2001 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower2001 : ∀ h, Pure node2001 h → 11 ≤ h.length := by
  apply indexed_extend node2001 [(1, node1617), (5, node1393), (6, node1367), (7, node1368), (10, node1356), (13, node1360)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1617
  · exact lower1393
  · exact lower1367
  · exact lower1368
  · exact lower1356
  · exact lower1360
def node2002 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower2002 : ∀ h, Pure node2002 h → 11 ≤ h.length := by
  apply indexed_extend node2002 [(1, node1618), (4, node1413), (7, node1370), (10, node1357), (12, node1356), (13, node1362), (14, node1353)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1618
  · exact lower1413
  · exact lower1370
  · exact lower1357
  · exact lower1356
  · exact lower1362
  · exact lower1353
def node2003 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower2003 : ∀ h, Pure node2003 h → 11 ≤ h.length := by
  apply indexed_extend node2003 [(1, node1619), (5, node1394), (6, node1369), (7, node1371), (10, node1357), (13, node1363), (14, node1354)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1619
  · exact lower1394
  · exact lower1369
  · exact lower1371
  · exact lower1357
  · exact lower1363
  · exact lower1354
def entries500 : List Graph := [node2000, node2001, node2002, node2003]
theorem entries_count500 : entries500.length = 4 := by decide +kernel
theorem arc_count500 : (entries500.map (fun g => ((verts g).filter (wye g)).length)).sum = 27 := by decide +kernel
end RawCert
