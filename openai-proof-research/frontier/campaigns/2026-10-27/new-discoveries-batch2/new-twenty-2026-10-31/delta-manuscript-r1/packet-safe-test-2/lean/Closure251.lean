import Closure250
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1004 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower1004 : ∀ h, Pure node1004 h → 11 ≤ h.length := by
  apply indexed_extend node1004 [(3, node357), (5, node415), (12, node306), (13, node303)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower357
  · exact lower415
  · exact lower306
  · exact lower303
def node1005 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower1005 : ∀ h, Pure node1005 h → 11 ≤ h.length := by
  apply indexed_extend node1005 [(3, node358), (7, node314), (12, node307), (13, node304)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower358
  · exact lower314
  · exact lower307
  · exact lower304
def node1006 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1006 : ∀ h, Pure node1006 h → 11 ≤ h.length := by
  apply indexed_extend node1006 [(1, node367), (2, node359), (5, node409)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower367
  · exact lower359
  · exact lower409
def node1007 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1007 : ∀ h, Pure node1007 h → 11 ≤ h.length := by
  apply indexed_extend node1007 [(1, node368), (2, node360), (7, node315)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower368
  · exact lower360
  · exact lower315
def entries251 : List Graph := [node1004, node1005, node1006, node1007]
theorem entries_count251 : entries251.length = 4 := by decide +kernel
theorem census_node1004 : ((verts node1004).filter (wye node1004)).length = 4 := by decide +kernel
theorem census_node1005 : ((verts node1005).filter (wye node1005)).length = 4 := by decide +kernel
theorem census_node1006 : ((verts node1006).filter (wye node1006)).length = 3 := by decide +kernel
theorem census_node1007 : ((verts node1007).filter (wye node1007)).length = 3 := by decide +kernel
theorem arc_count251 : (entries251.map (fun g => ((verts g).filter (wye g)).length)).sum = 14 := by
  simp only [entries251, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1004, census_node1005, census_node1006, census_node1007]
  decide +kernel
end RawCert
