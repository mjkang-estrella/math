import Closure236
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node948 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower948 : ∀ h, Pure node948 h → 11 ≤ h.length := by
  apply indexed_extend node948 [(3, node273), (8, node270), (11, node265), (12, node264)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower273
  · exact lower270
  · exact lower265
  · exact lower264
def node949 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [0, 0, 1, 2, 0, 1, 0, 1, 0, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower949 : ∀ h, Pure node949 h → 11 ≤ h.length := by
  apply indexed_extend node949 [(3, node274), (8, node271), (11, node266)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower274
  · exact lower271
  · exact lower266
def node950 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower950 : ∀ h, Pure node950 h → 11 ≤ h.length := by
  apply indexed_extend node950 [(8, node271)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower271
def node951 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 3, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower951 : ∀ h, Pure node951 h → 11 ≤ h.length := by
  apply indexed_extend node951 [(4, node273), (12, node267)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower273
  · exact lower267
def entries237 : List Graph := [node948, node949, node950, node951]
theorem entries_count237 : entries237.length = 4 := by decide +kernel
theorem census_node948 : ((verts node948).filter (wye node948)).length = 4 := by decide +kernel
theorem census_node949 : ((verts node949).filter (wye node949)).length = 3 := by decide +kernel
theorem census_node950 : ((verts node950).filter (wye node950)).length = 1 := by decide +kernel
theorem census_node951 : ((verts node951).filter (wye node951)).length = 2 := by decide +kernel
theorem arc_count237 : (entries237.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries237, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node948, census_node949, census_node950, census_node951]
  decide +kernel
end RawCert
