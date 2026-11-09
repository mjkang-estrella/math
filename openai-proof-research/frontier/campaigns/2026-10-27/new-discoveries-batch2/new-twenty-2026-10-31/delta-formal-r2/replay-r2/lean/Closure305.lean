import Closure304
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1220 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower1220 : ∀ h, Pure node1220 h → 11 ≤ h.length := by
  apply indexed_extend node1220 [(0, node969), (3, node357), (6, node481), (13, node475)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower969
  · exact lower357
  · exact lower481
  · exact lower475
def node1221 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0], [0, 0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower1221 : ∀ h, Pure node1221 h → 11 ≤ h.length := by
  apply indexed_extend node1221 [(0, node970), (3, node358), (7, node482), (11, node598), (13, node476)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower970
  · exact lower358
  · exact lower482
  · exact lower598
  · exact lower476
def node1222 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1222 : ∀ h, Pure node1222 h → 11 ≤ h.length := by
  apply indexed_extend node1222 [(0, node900), (1, node728), (5, node552), (12, node479), (13, node477)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower900
  · exact lower728
  · exact lower552
  · exact lower479
  · exact lower477
def node1223 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 2, 0, 0]]
theorem lower1223 : ∀ h, Pure node1223 h → 11 ≤ h.length := by
  apply indexed_extend node1223 [(0, node901), (1, node729), (3, node373), (10, node585), (12, node480)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower901
  · exact lower729
  · exact lower373
  · exact lower585
  · exact lower480
def entries305 : List Graph := [node1220, node1221, node1222, node1223]
theorem entries_count305 : entries305.length = 4 := by decide +kernel
theorem arc_count305 : (entries305.map (fun g => ((verts g).filter (wye g)).length)).sum = 19 := by decide +kernel
end RawCert
