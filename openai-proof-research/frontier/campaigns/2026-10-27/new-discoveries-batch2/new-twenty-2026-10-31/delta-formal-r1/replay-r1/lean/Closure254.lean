import Closure253
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1016 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower1016 : ∀ h, Pure node1016 h → 11 ≤ h.length := by
  apply indexed_extend node1016 [(4, node419), (6, node326), (8, node321), (9, node322)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower419
  · exact lower326
  · exact lower321
  · exact lower322
def node1017 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3], [0, 1, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 0]]
theorem lower1017 : ∀ h, Pure node1017 h → 11 ≤ h.length := by
  apply indexed_extend node1017 [(3, node485), (7, node327), (8, node324), (9, node325)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower485
  · exact lower327
  · exact lower324
  · exact lower325
def node1018 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1018 : ∀ h, Pure node1018 h → 11 ≤ h.length := by
  apply indexed_extend node1018 [(2, node492), (4, node659), (7, node335), (9, node328)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower492
  · exact lower659
  · exact lower335
  · exact lower328
def node1019 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1], [2, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1019 : ∀ h, Pure node1019 h → 11 ≤ h.length := by
  apply indexed_extend node1019 [(2, node493), (7, node336), (9, node329)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower493
  · exact lower336
  · exact lower329
def entries254 : List Graph := [node1016, node1017, node1018, node1019]
theorem entries_count254 : entries254.length = 4 := by decide +kernel
theorem arc_count254 : (entries254.map (fun g => ((verts g).filter (wye g)).length)).sum = 15 := by decide +kernel
end RawCert
