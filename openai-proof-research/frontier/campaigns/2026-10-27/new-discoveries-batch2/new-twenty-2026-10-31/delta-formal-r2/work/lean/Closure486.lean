import Closure485
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1944 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower1944 : ∀ h, Pure node1944 h → 11 ≤ h.length := by
  apply indexed_extend node1944 [(2, node1547), (3, node1113), (6, node1287), (7, node1288), (8, node1289), (11, node1270), (12, node1403), (13, node1263)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1547
  · exact lower1113
  · exact lower1287
  · exact lower1288
  · exact lower1289
  · exact lower1270
  · exact lower1403
  · exact lower1263
def node1945 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1945 : ∀ h, Pure node1945 h → 11 ≤ h.length := by
  apply indexed_extend node1945 [(3, node1114), (5, node1290), (6, node1291), (8, node1296), (10, node1271), (13, node1256), (14, node1255)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1114
  · exact lower1290
  · exact lower1291
  · exact lower1296
  · exact lower1271
  · exact lower1256
  · exact lower1255
def node1946 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1946 : ∀ h, Pure node1946 h → 11 ≤ h.length := by
  apply indexed_extend node1946 [(3, node1126), (5, node1292), (6, node1293), (8, node1290), (10, node1272), (12, node1404), (13, node1258), (14, node1257)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1126
  · exact lower1292
  · exact lower1293
  · exact lower1290
  · exact lower1272
  · exact lower1404
  · exact lower1258
  · exact lower1257
def node1947 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1947 : ∀ h, Pure node1947 h → 11 ≤ h.length := by
  apply indexed_extend node1947 [(5, node1292), (7, node1294), (8, node1291), (10, node1273), (12, node1405), (13, node1260), (14, node1259)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1292
  · exact lower1294
  · exact lower1291
  · exact lower1273
  · exact lower1405
  · exact lower1260
  · exact lower1259
def entries486 : List Graph := [node1944, node1945, node1946, node1947]
theorem entries_count486 : entries486.length = 4 := by decide +kernel
theorem arc_count486 : (entries486.map (fun g => ((verts g).filter (wye g)).length)).sum = 30 := by decide +kernel
end RawCert
