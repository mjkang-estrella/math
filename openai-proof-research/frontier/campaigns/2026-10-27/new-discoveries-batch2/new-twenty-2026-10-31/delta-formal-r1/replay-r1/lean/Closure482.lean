import Closure481
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1928 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1928 : ∀ h, Pure node1928 h → 11 ≤ h.length := by
  apply indexed_extend node1928 [(2, node1532), (5, node1253), (7, node1249), (8, node1250), (10, node1248), (14, node1235)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1532
  · exact lower1253
  · exact lower1249
  · exact lower1250
  · exact lower1248
  · exact lower1235
def node1929 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1929 : ∀ h, Pure node1929 h → 11 ≤ h.length := by
  apply indexed_extend node1929 [(1, node1532), (5, node1254), (7, node1251), (8, node1252), (13, node1237), (14, node1236)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1532
  · exact lower1254
  · exact lower1251
  · exact lower1252
  · exact lower1237
  · exact lower1236
def node1930 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0]]
theorem lower1930 : ∀ h, Pure node1930 h → 11 ≤ h.length := by
  apply indexed_extend node1930 [(3, node1103), (5, node1257), (6, node1259), (8, node1262), (9, node1255), (11, node1238), (13, node1388)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1103
  · exact lower1257
  · exact lower1259
  · exact lower1262
  · exact lower1255
  · exact lower1238
  · exact lower1388
def node1931 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower1931 : ∀ h, Pure node1931 h → 11 ≤ h.length := by
  apply indexed_extend node1931 [(3, node1104), (5, node1258), (6, node1260), (7, node1261), (8, node1263), (9, node1256), (13, node1389)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1104
  · exact lower1258
  · exact lower1260
  · exact lower1261
  · exact lower1263
  · exact lower1256
  · exact lower1389
def entries482 : List Graph := [node1928, node1929, node1930, node1931]
theorem entries_count482 : entries482.length = 4 := by decide +kernel
theorem arc_count482 : (entries482.map (fun g => ((verts g).filter (wye g)).length)).sum = 26 := by decide +kernel
end RawCert
