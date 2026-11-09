import Closure232
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node932 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 0, 1], [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0], [1, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0]]
theorem lower932 : ∀ h, Pure node932 h → 11 ≤ h.length := by
  apply indexed_extend node932 [(4, node263), (8, node262)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower263
  · exact lower262
def node933 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 1, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [1, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower933 : ∀ h, Pure node933 h → 11 ≤ h.length := by
  apply indexed_extend node933 [(3, node269), (4, node264), (7, node275), (9, node262)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower269
  · exact lower264
  · exact lower275
  · exact lower262
def node934 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower934 : ∀ h, Pure node934 h → 11 ≤ h.length := by
  apply indexed_extend node934 [(4, node265), (7, node276)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower265
  · exact lower276
def node935 : Graph := [[0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 1, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 1], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 2, 0, 0]]
theorem lower935 : ∀ h, Pure node935 h → 11 ≤ h.length := by
  apply indexed_extend node935 [(4, node266), (7, node277)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower266
  · exact lower277
def entries233 : List Graph := [node932, node933, node934, node935]
theorem entries_count233 : entries233.length = 4 := by decide +kernel
theorem census_node932 : ((verts node932).filter (wye node932)).length = 2 := by decide +kernel
theorem census_node933 : ((verts node933).filter (wye node933)).length = 4 := by decide +kernel
theorem census_node934 : ((verts node934).filter (wye node934)).length = 2 := by decide +kernel
theorem census_node935 : ((verts node935).filter (wye node935)).length = 2 := by decide +kernel
theorem arc_count233 : (entries233.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries233, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node932, census_node933, census_node934, census_node935]
  decide +kernel
end RawCert
