import Closure200
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node804 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 2, 0, 0]]
theorem lower804 : ∀ h, Pure node804 h → 11 ≤ h.length := by
  apply indexed_extend node804 [(7, node215), (10, node207)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower215
  · exact lower207
def node805 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0]]
theorem lower805 : ∀ h, Pure node805 h → 11 ≤ h.length := by
  apply indexed_extend node805 [(5, node233), (9, node208)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower233
  · exact lower208
def node806 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 2, 0, 0]]
theorem lower806 : ∀ h, Pure node806 h → 11 ≤ h.length := by
  apply indexed_extend node806 [(9, node208)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower208
def node807 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [1, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 1, 0]]
theorem lower807 : ∀ h, Pure node807 h → 11 ≤ h.length := by
  apply indexed_extend node807 [(5, node234), (6, node212), (7, node213), (9, node209)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower234
  · exact lower212
  · exact lower213
  · exact lower209
def entries201 : List Graph := [node804, node805, node806, node807]
theorem entries_count201 : entries201.length = 4 := by decide +kernel
theorem arc_count201 : (entries201.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by decide +kernel
end RawCert
