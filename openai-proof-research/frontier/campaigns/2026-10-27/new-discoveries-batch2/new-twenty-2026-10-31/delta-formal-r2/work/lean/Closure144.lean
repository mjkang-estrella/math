import Closure143
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node576 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 2, 0]]
theorem lower576 : ∀ h, Pure node576 h → 11 ≤ h.length := by
  apply indexed_extend node576 [(4, node126), (11, node118)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower126
  · exact lower118
def node577 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 1, 0], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 2], [0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower577 : ∀ h, Pure node577 h → 11 ≤ h.length := by
  apply indexed_extend node577 [(1, node216), (12, node119)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower216
  · exact lower119
def node578 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2], [2, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0]]
theorem lower578 : ∀ h, Pure node578 h → 11 ≤ h.length := by
  apply indexed_extend node578 [(4, node140), (10, node119)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower140
  · exact lower119
def node579 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 1], [2, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0]]
theorem lower579 : ∀ h, Pure node579 h → 11 ≤ h.length := by
  apply indexed_extend node579 [(7, node121)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower121
def entries144 : List Graph := [node576, node577, node578, node579]
theorem entries_count144 : entries144.length = 4 := by decide +kernel
theorem arc_count144 : (entries144.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by decide +kernel
end RawCert
