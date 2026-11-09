import Closure482
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1932 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1932 : ∀ h, Pure node1932 h → 11 ≤ h.length := by
  apply indexed_extend node1932 [(1, node1535), (2, node1533), (3, node1105), (5, node1266), (6, node1267), (9, node1264), (12, node1385), (14, node1238)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1535
  · exact lower1533
  · exact lower1105
  · exact lower1266
  · exact lower1267
  · exact lower1264
  · exact lower1385
  · exact lower1238
def node1933 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 1, 0]]
theorem lower1933 : ∀ h, Pure node1933 h → 11 ≤ h.length := by
  apply indexed_extend node1933 [(1, node1536), (2, node1534), (3, node1106), (6, node1268), (7, node1269), (8, node1270), (9, node1265), (12, node1386)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1536
  · exact lower1534
  · exact lower1106
  · exact lower1268
  · exact lower1269
  · exact lower1270
  · exact lower1265
  · exact lower1386
def node1934 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1934 : ∀ h, Pure node1934 h → 11 ≤ h.length := by
  apply indexed_extend node1934 [(3, node1107), (5, node1272), (6, node1273), (7, node1274), (9, node1271), (12, node1390), (14, node1238)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1107
  · exact lower1272
  · exact lower1273
  · exact lower1274
  · exact lower1271
  · exact lower1390
  · exact lower1238
def node1935 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1935 : ∀ h, Pure node1935 h → 11 ≤ h.length := by
  apply indexed_extend node1935 [(1, node1538), (2, node1537), (3, node1108), (6, node1276), (7, node1277), (9, node1275), (11, node1387)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1538
  · exact lower1537
  · exact lower1108
  · exact lower1276
  · exact lower1277
  · exact lower1275
  · exact lower1387
def entries483 : List Graph := [node1932, node1933, node1934, node1935]
theorem entries_count483 : entries483.length = 4 := by decide +kernel
theorem arc_count483 : (entries483.map (fun g => ((verts g).filter (wye g)).length)).sum = 30 := by decide +kernel
end RawCert
