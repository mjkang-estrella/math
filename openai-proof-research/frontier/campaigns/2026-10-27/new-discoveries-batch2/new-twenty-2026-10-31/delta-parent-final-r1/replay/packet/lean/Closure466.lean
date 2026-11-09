import Closure465
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1864 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower1864 : ∀ h, Pure node1864 h → 11 ≤ h.length := by
  apply indexed_extend node1864 [(0, node1732), (3, node1001), (4, node1217), (5, node1214), (8, node1183), (10, node1181), (12, node1340), (13, node1162)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1732
  · exact lower1001
  · exact lower1217
  · exact lower1214
  · exact lower1183
  · exact lower1181
  · exact lower1340
  · exact lower1162
def node1865 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower1865 : ∀ h, Pure node1865 h → 11 ≤ h.length := by
  apply indexed_extend node1865 [(0, node1733), (3, node1002), (5, node1215), (6, node1274), (10, node1181), (12, node1341)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1733
  · exact lower1002
  · exact lower1215
  · exact lower1274
  · exact lower1181
  · exact lower1341
def node1866 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1866 : ∀ h, Pure node1866 h → 11 ≤ h.length := by
  apply indexed_extend node1866 [(0, node1743), (4, node1218), (6, node1294), (8, node1182), (12, node1351), (13, node1164), (14, node1163)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1743
  · exact lower1218
  · exact lower1294
  · exact lower1182
  · exact lower1351
  · exact lower1164
  · exact lower1163
def node1867 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 2, 0]]
theorem lower1867 : ∀ h, Pure node1867 h → 11 ≤ h.length := by
  apply indexed_extend node1867 [(0, node1744), (3, node1003), (4, node1219), (6, node1295), (9, node1183), (12, node1352), (13, node1167)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1744
  · exact lower1003
  · exact lower1219
  · exact lower1295
  · exact lower1183
  · exact lower1352
  · exact lower1167
def entries466 : List Graph := [node1864, node1865, node1866, node1867]
theorem entries_count466 : entries466.length = 4 := by decide +kernel
theorem arc_count466 : (entries466.map (fun g => ((verts g).filter (wye g)).length)).sum = 28 := by decide +kernel
end RawCert
