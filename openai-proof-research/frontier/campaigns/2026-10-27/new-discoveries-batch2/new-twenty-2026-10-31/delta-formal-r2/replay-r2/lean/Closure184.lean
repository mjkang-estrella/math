import Closure183
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node736 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower736 : ∀ h, Pure node736 h → 11 ≤ h.length := by
  apply indexed_extend node736 [(0, node175), (8, node184), (12, node183)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower175
  · exact lower184
  · exact lower183
def node737 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0, 0]]
theorem lower737 : ∀ h, Pure node737 h → 11 ≤ h.length := by
  apply indexed_extend node737 [(0, node176), (2, node107), (8, node185), (9, node227)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower176
  · exact lower107
  · exact lower185
  · exact lower227
def node738 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower738 : ∀ h, Pure node738 h → 11 ≤ h.length := by
  apply indexed_extend node738 [(0, node178)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower178
def node739 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower739 : ∀ h, Pure node739 h → 11 ≤ h.length := by
  apply indexed_extend node739 [(0, node179), (2, node108), (9, node223)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower179
  · exact lower108
  · exact lower223
def entries184 : List Graph := [node736, node737, node738, node739]
theorem entries_count184 : entries184.length = 4 := by decide +kernel
theorem arc_count184 : (entries184.map (fun g => ((verts g).filter (wye g)).length)).sum = 11 := by decide +kernel
end RawCert
