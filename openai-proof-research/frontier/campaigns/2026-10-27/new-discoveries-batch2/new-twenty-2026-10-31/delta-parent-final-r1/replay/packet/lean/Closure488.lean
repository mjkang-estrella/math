import Closure487
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1952 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1952 : ∀ h, Pure node1952 h → 11 ≤ h.length := by
  apply indexed_extend node1952 [(1, node1553), (3, node1127), (5, node1300), (6, node1301), (8, node1297), (11, node1394), (13, node1272), (14, node1266)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1553
  · exact lower1127
  · exact lower1300
  · exact lower1301
  · exact lower1297
  · exact lower1394
  · exact lower1272
  · exact lower1266
def node1953 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1953 : ∀ h, Pure node1953 h → 11 ≤ h.length := by
  apply indexed_extend node1953 [(1, node1563), (2, node1556), (7, node1302), (8, node1298), (10, node1276), (11, node1395), (12, node1268)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1563
  · exact lower1556
  · exact lower1302
  · exact lower1298
  · exact lower1276
  · exact lower1395
  · exact lower1268
def node1954 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1954 : ∀ h, Pure node1954 h → 11 ≤ h.length := by
  apply indexed_extend node1954 [(1, node1564), (2, node1557), (5, node1300), (8, node1299), (10, node1276), (11, node1397), (13, node1273), (14, node1267)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1564
  · exact lower1557
  · exact lower1300
  · exact lower1299
  · exact lower1276
  · exact lower1397
  · exact lower1273
  · exact lower1267
def node1955 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower1955 : ∀ h, Pure node1955 h → 11 ≤ h.length := by
  apply indexed_extend node1955 [(1, node1565), (2, node1558), (3, node1119), (7, node1303), (10, node1277), (11, node1398), (12, node1269)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower1565
  · exact lower1558
  · exact lower1119
  · exact lower1303
  · exact lower1277
  · exact lower1398
  · exact lower1269
def entries488 : List Graph := [node1952, node1953, node1954, node1955]
theorem entries_count488 : entries488.length = 4 := by decide +kernel
theorem arc_count488 : (entries488.map (fun g => ((verts g).filter (wye g)).length)).sum = 30 := by decide +kernel
end RawCert
