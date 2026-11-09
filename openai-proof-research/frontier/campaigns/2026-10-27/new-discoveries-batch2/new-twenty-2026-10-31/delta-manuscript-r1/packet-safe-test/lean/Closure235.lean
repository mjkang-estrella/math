import Closure234
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node940 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2], [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower940 : ∀ h, Pure node940 h → 11 ≤ h.length := by
  apply indexed_extend node940 [(4, node270), (12, node262)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower270
  · exact lower262
def node941 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 2, 0]]
theorem lower941 : ∀ h, Pure node941 h → 11 ≤ h.length := by
  apply indexed_extend node941 [(4, node271)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower271
def node942 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0]]
theorem lower942 : ∀ h, Pure node942 h → 11 ≤ h.length := by
  apply indexed_extend node942 [(3, node272), (7, node264), (9, node263)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower272
  · exact lower264
  · exact lower263
def node943 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower943 : ∀ h, Pure node943 h → 11 ≤ h.length := by
  apply indexed_extend node943 [(7, node265)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower265
def entries235 : List Graph := [node940, node941, node942, node943]
theorem entries_count235 : entries235.length = 4 := by decide +kernel
theorem census_node940 : ((verts node940).filter (wye node940)).length = 2 := by decide +kernel
theorem census_node941 : ((verts node941).filter (wye node941)).length = 1 := by decide +kernel
theorem census_node942 : ((verts node942).filter (wye node942)).length = 3 := by decide +kernel
theorem census_node943 : ((verts node943).filter (wye node943)).length = 1 := by decide +kernel
theorem arc_count235 : (entries235.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by
  simp only [entries235, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node940, census_node941, census_node942, census_node943]
  decide +kernel
end RawCert
