import Closure212
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node852 : Graph := [[0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1, 0], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower852 : ∀ h, Pure node852 h → 11 ≤ h.length := by
  apply indexed_extend node852 [(5, node229)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower229
def node853 : Graph := [[0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 1, 0]]
theorem lower853 : ∀ h, Pure node853 h → 11 ≤ h.length := by
  apply indexed_extend node853 [(5, node230), (6, node232), (7, node234)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower230
  · exact lower232
  · exact lower234
def node854 : Graph := [[0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower854 : ∀ h, Pure node854 h → 11 ≤ h.length := by
  apply indexed_extend node854 [(5, node231), (6, node233)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower231
  · exact lower233
def node855 : Graph := [[0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1, 0], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0]]
theorem lower855 : ∀ h, Pure node855 h → 11 ≤ h.length := by
  apply indexed_extend node855 [(4, node228), (5, node235)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower228
  · exact lower235
def entries213 : List Graph := [node852, node853, node854, node855]
theorem entries_count213 : entries213.length = 4 := by decide +kernel
theorem arc_count213 : (entries213.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by decide +kernel
end RawCert
