import Closure077
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node312 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1, 1, 1, 2, 0, 0, 0]]
theorem lower312 : ∀ h, Pure node312 h → 11 ≤ h.length := by
  apply indexed_extend node312 [(2, node49), (9, node36), (11, node35)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower49
  · exact lower36
  · exact lower35
def node313 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 2, 0]]
theorem lower313 : ∀ h, Pure node313 h → 11 ≤ h.length := by
  apply indexed_extend node313 [(4, node51)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower51
def node314 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0]]
theorem lower314 : ∀ h, Pure node314 h → 11 ≤ h.length := by
  apply indexed_extend node314 [(3, node52), (11, node35)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower52
  · exact lower35
def node315 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0]]
theorem lower315 : ∀ h, Pure node315 h → 11 ≤ h.length := by
  apply indexed_extend node315 [(1, node55), (2, node53)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower55
  · exact lower53
def entries78 : List Graph := [node312, node313, node314, node315]
theorem entries_count78 : entries78.length = 4 := by decide +kernel
theorem census_node312 : ((verts node312).filter (wye node312)).length = 3 := by decide +kernel
theorem census_node313 : ((verts node313).filter (wye node313)).length = 1 := by decide +kernel
theorem census_node314 : ((verts node314).filter (wye node314)).length = 2 := by decide +kernel
theorem census_node315 : ((verts node315).filter (wye node315)).length = 2 := by decide +kernel
theorem arc_count78 : (entries78.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by
  simp only [entries78, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node312, census_node313, census_node314, census_node315]
  decide +kernel
end RawCert
