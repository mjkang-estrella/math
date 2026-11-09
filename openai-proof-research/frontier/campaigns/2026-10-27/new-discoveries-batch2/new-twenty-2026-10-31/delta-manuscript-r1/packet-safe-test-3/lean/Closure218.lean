import Closure217
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node872 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower872 : ∀ h, Pure node872 h → 11 ≤ h.length := by
  apply indexed_extend node872 [(9, node237), (10, node236)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower237
  · exact lower236
def node873 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower873 : ∀ h, Pure node873 h → 11 ≤ h.length := by
  apply indexed_extend node873 [(4, node241), (10, node236)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower241
  · exact lower236
def node874 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower874 : ∀ h, Pure node874 h → 11 ≤ h.length := by
  apply indexed_extend node874 [(4, node243), (9, node237), (12, node235)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower243
  · exact lower237
  · exact lower235
def node875 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower875 : ∀ h, Pure node875 h → 11 ≤ h.length := by
  apply indexed_extend node875 [(9, node239), (10, node238)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower239
  · exact lower238
def entries218 : List Graph := [node872, node873, node874, node875]
theorem entries_count218 : entries218.length = 4 := by decide +kernel
theorem census_node872 : ((verts node872).filter (wye node872)).length = 2 := by decide +kernel
theorem census_node873 : ((verts node873).filter (wye node873)).length = 2 := by decide +kernel
theorem census_node874 : ((verts node874).filter (wye node874)).length = 3 := by decide +kernel
theorem census_node875 : ((verts node875).filter (wye node875)).length = 2 := by decide +kernel
theorem arc_count218 : (entries218.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries218, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node872, census_node873, census_node874, census_node875]
  decide +kernel
end RawCert
