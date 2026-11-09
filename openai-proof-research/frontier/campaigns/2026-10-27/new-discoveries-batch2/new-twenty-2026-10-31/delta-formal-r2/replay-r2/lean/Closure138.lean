import Closure137
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node552 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0], [1, 0, 0, 1, 1, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower552 : ∀ h, Pure node552 h → 11 ≤ h.length := by
  apply indexed_extend node552 [(1, node204), (11, node115), (12, node113)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower204
  · exact lower115
  · exact lower113
def node553 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 2], [1, 0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1, 0]]
theorem lower553 : ∀ h, Pure node553 h → 11 ≤ h.length := by
  apply indexed_extend node553 [(2, node205), (10, node114)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower205
  · exact lower114
def node554 : Graph := [[0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0]]
theorem lower554 : ∀ h, Pure node554 h → 11 ≤ h.length := by
  apply indexed_extend node554 [(0, node267), (3, node91), (5, node116)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower267
  · exact lower91
  · exact lower116
def node555 : Graph := [[0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1], [0, 0, 0, 2, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0]]
theorem lower555 : ∀ h, Pure node555 h → 11 ≤ h.length := by
  apply indexed_extend node555 [(0, node268), (3, node92), (11, node140)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower268
  · exact lower92
  · exact lower140
def entries138 : List Graph := [node552, node553, node554, node555]
theorem entries_count138 : entries138.length = 4 := by decide +kernel
theorem arc_count138 : (entries138.map (fun g => ((verts g).filter (wye g)).length)).sum = 11 := by decide +kernel
end RawCert
