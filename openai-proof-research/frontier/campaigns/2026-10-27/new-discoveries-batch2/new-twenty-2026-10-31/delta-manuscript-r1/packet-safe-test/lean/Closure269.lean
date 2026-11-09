import Closure268
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1076 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1076 : ∀ h, Pure node1076 h → 11 ≤ h.length := by
  apply indexed_extend node1076 [(1, node508), (4, node428), (8, node373), (12, node354)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower508
  · exact lower428
  · exact lower373
  · exact lower354
def node1077 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower1077 : ∀ h, Pure node1077 h → 11 ≤ h.length := by
  apply indexed_extend node1077 [(1, node519), (2, node511), (6, node375), (8, node374)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower519
  · exact lower511
  · exact lower375
  · exact lower374
def node1078 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1078 : ∀ h, Pure node1078 h → 11 ≤ h.length := by
  apply indexed_extend node1078 [(1, node520), (2, node512), (3, node521), (6, node378), (9, node374), (12, node355)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower520
  · exact lower512
  · exact lower521
  · exact lower378
  · exact lower374
  · exact lower355
def node1079 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1079 : ∀ h, Pure node1079 h → 11 ≤ h.length := by
  apply indexed_extend node1079 [(2, node513), (6, node375), (7, node376), (8, node377)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower513
  · exact lower375
  · exact lower376
  · exact lower377
def entries269 : List Graph := [node1076, node1077, node1078, node1079]
theorem entries_count269 : entries269.length = 4 := by decide +kernel
theorem census_node1076 : ((verts node1076).filter (wye node1076)).length = 4 := by decide +kernel
theorem census_node1077 : ((verts node1077).filter (wye node1077)).length = 4 := by decide +kernel
theorem census_node1078 : ((verts node1078).filter (wye node1078)).length = 6 := by decide +kernel
theorem census_node1079 : ((verts node1079).filter (wye node1079)).length = 4 := by decide +kernel
theorem arc_count269 : (entries269.map (fun g => ((verts g).filter (wye g)).length)).sum = 18 := by
  simp only [entries269, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1076, census_node1077, census_node1078, census_node1079]
  decide +kernel
end RawCert
