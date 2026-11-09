import Closure223
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node896 : Graph := [[0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0], [0, 0, 2, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 0, 3, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower896 : ∀ h, Pure node896 h → 11 ≤ h.length := by
  apply indexed_extend node896 [(0, node30), (12, node268)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower30
  · exact lower268
def node897 : Graph := [[0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower897 : ∀ h, Pure node897 h → 11 ≤ h.length := by
  apply indexed_extend node897 [(0, node177), (1, node143), (3, node254), (6, node257), (12, node269)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower177
  · exact lower143
  · exact lower254
  · exact lower257
  · exact lower269
def node898 : Graph := [[0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower898 : ∀ h, Pure node898 h → 11 ≤ h.length := by
  apply indexed_extend node898 [(0, node31), (11, node265)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower31
  · exact lower265
def node899 : Graph := [[0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [0, 0, 1, 2, 0, 1, 0, 1, 0, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1, 1, 2, 0, 0, 0]]
theorem lower899 : ∀ h, Pure node899 h → 11 ≤ h.length := by
  apply indexed_extend node899 [(0, node32), (11, node266)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower32
  · exact lower266
def entries224 : List Graph := [node896, node897, node898, node899]
theorem entries_count224 : entries224.length = 4 := by decide +kernel
theorem arc_count224 : (entries224.map (fun g => ((verts g).filter (wye g)).length)).sum = 11 := by decide +kernel
end RawCert
