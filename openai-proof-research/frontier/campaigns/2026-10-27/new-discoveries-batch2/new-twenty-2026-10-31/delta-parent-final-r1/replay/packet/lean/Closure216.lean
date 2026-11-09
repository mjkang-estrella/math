import Closure215
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node864 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower864 : ∀ h, Pure node864 h → 11 ≤ h.length := by
  apply indexed_extend node864 [(9, node231), (12, node229)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower231
  · exact lower229
def node865 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower865 : ∀ h, Pure node865 h → 11 ≤ h.length := by
  apply indexed_extend node865 [(6, node248), (9, node233), (10, node232)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower248
  · exact lower233
  · exact lower232
def node866 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 0]]
theorem lower866 : ∀ h, Pure node866 h → 11 ≤ h.length := by
  apply indexed_extend node866 [(6, node249), (10, node232)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower249
  · exact lower232
def node867 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0, 0]]
theorem lower867 : ∀ h, Pure node867 h → 11 ≤ h.length := by
  apply indexed_extend node867 [(9, node233)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower233
def entries216 : List Graph := [node864, node865, node866, node867]
theorem entries_count216 : entries216.length = 4 := by decide +kernel
theorem arc_count216 : (entries216.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by decide +kernel
end RawCert
