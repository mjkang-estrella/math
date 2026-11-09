import Closure486
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1948 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0]]
theorem lower1948 : ∀ h, Pure node1948 h → 11 ≤ h.length := by
  apply indexed_extend node1948 [(3, node1115), (5, node1293), (7, node1295), (10, node1274), (12, node1406), (13, node1261)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1115
  · exact lower1293
  · exact lower1295
  · exact lower1274
  · exact lower1406
  · exact lower1261
def node1949 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1949 : ∀ h, Pure node1949 h → 11 ≤ h.length := by
  apply indexed_extend node1949 [(3, node1116), (6, node1294), (7, node1295), (8, node1296), (12, node1407), (13, node1263), (14, node1262)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1116
  · exact lower1294
  · exact lower1295
  · exact lower1296
  · exact lower1407
  · exact lower1263
  · exact lower1262
def node1950 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1950 : ∀ h, Pure node1950 h → 11 ≤ h.length := by
  apply indexed_extend node1950 [(1, node1561), (2, node1554), (3, node1117), (6, node1298), (8, node1304), (10, node1275), (12, node1265)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1561
  · exact lower1554
  · exact lower1117
  · exact lower1298
  · exact lower1304
  · exact lower1275
  · exact lower1265
def node1951 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1951 : ∀ h, Pure node1951 h → 11 ≤ h.length := by
  apply indexed_extend node1951 [(1, node1562), (2, node1555), (3, node1118), (5, node1297), (6, node1299), (10, node1275), (13, node1271), (14, node1264)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1562
  · exact lower1555
  · exact lower1118
  · exact lower1297
  · exact lower1299
  · exact lower1275
  · exact lower1271
  · exact lower1264
def entries487 : List Graph := [node1948, node1949, node1950, node1951]
theorem entries_count487 : entries487.length = 4 := by decide +kernel
theorem arc_count487 : (entries487.map (fun g => ((verts g).filter (wye g)).length)).sum = 28 := by decide +kernel
end RawCert
