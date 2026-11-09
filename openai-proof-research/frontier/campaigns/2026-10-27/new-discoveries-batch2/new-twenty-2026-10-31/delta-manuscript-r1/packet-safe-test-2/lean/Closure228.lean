import Closure227
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node912 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0]]
theorem lower912 : ∀ h, Pure node912 h → 11 ≤ h.length := by
  apply indexed_extend node912 [(1, node80), (9, node255), (11, node276)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower80
  · exact lower255
  · exact lower276
def node913 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 1, 1, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 0, 1, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower913 : ∀ h, Pure node913 h → 11 ≤ h.length := by
  apply indexed_extend node913 [(1, node81), (3, node258), (10, node255)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower81
  · exact lower258
  · exact lower255
def node914 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 1, 1, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1, 1, 1, 2, 0, 0, 0]]
theorem lower914 : ∀ h, Pure node914 h → 11 ≤ h.length := by
  apply indexed_extend node914 [(1, node82), (9, node256), (11, node277)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower82
  · exact lower256
  · exact lower277
def node915 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 1, 2, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower915 : ∀ h, Pure node915 h → 11 ≤ h.length := by
  apply indexed_extend node915 [(1, node83), (3, node259), (10, node256)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower83
  · exact lower259
  · exact lower256
def entries228 : List Graph := [node912, node913, node914, node915]
theorem entries_count228 : entries228.length = 4 := by decide +kernel
theorem census_node912 : ((verts node912).filter (wye node912)).length = 3 := by decide +kernel
theorem census_node913 : ((verts node913).filter (wye node913)).length = 3 := by decide +kernel
theorem census_node914 : ((verts node914).filter (wye node914)).length = 3 := by decide +kernel
theorem census_node915 : ((verts node915).filter (wye node915)).length = 3 := by decide +kernel
theorem arc_count228 : (entries228.map (fun g => ((verts g).filter (wye g)).length)).sum = 12 := by
  simp only [entries228, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node912, census_node913, census_node914, census_node915]
  decide +kernel
end RawCert
