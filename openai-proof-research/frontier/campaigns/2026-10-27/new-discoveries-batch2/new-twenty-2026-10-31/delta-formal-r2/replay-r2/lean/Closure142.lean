import Closure141
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node568 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 2, 0]]
theorem lower568 : ∀ h, Pure node568 h → 11 ≤ h.length := by
  apply indexed_extend node568 [(8, node118)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower118
def node569 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [1, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 1, 0]]
theorem lower569 : ∀ h, Pure node569 h → 11 ≤ h.length := by
  apply indexed_extend node569 [(2, node212), (6, node130)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower212
  · exact lower130
def node570 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0]]
theorem lower570 : ∀ h, Pure node570 h → 11 ≤ h.length := by
  apply indexed_extend node570 [(2, node213), (6, node131), (9, node117)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower213
  · exact lower131
  · exact lower117
def node571 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [2, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 2, 1, 0]]
theorem lower571 : ∀ h, Pure node571 h → 11 ≤ h.length := by
  apply indexed_extend node571 [(2, node214), (4, node124), (10, node117)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower214
  · exact lower124
  · exact lower117
def entries142 : List Graph := [node568, node569, node570, node571]
theorem entries_count142 : entries142.length = 4 := by decide +kernel
theorem arc_count142 : (entries142.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by decide +kernel
end RawCert
