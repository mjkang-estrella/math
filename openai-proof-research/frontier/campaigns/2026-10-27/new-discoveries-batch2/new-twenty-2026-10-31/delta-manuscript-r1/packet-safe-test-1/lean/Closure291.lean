import Closure290
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1164 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0], [0, 0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower1164 : ∀ h, Pure node1164 h → 11 ≤ h.length := by
  apply indexed_extend node1164 [(0, node958), (6, node530), (8, node463), (12, node574)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower958
  · exact lower530
  · exact lower463
  · exact lower574
def node1165 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1], [0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 0]]
theorem lower1165 : ∀ h, Pure node1165 h → 11 ≤ h.length := by
  apply indexed_extend node1165 [(0, node959), (3, node303), (4, node475), (6, node531), (7, node462)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower959
  · exact lower303
  · exact lower475
  · exact lower531
  · exact lower462
def node1166 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 0]]
theorem lower1166 : ∀ h, Pure node1166 h → 11 ≤ h.length := by
  apply indexed_extend node1166 [(0, node960), (3, node304), (4, node476), (12, node567)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower960
  · exact lower304
  · exact lower476
  · exact lower567
def node1167 : Graph := [[0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 1], [0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 2, 0, 0]]
theorem lower1167 : ∀ h, Pure node1167 h → 11 ≤ h.length := by
  apply indexed_extend node1167 [(0, node961), (3, node305), (6, node532), (9, node464), (12, node575)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower961
  · exact lower305
  · exact lower532
  · exact lower464
  · exact lower575
def entries291 : List Graph := [node1164, node1165, node1166, node1167]
theorem entries_count291 : entries291.length = 4 := by decide +kernel
theorem census_node1164 : ((verts node1164).filter (wye node1164)).length = 4 := by decide +kernel
theorem census_node1165 : ((verts node1165).filter (wye node1165)).length = 5 := by decide +kernel
theorem census_node1166 : ((verts node1166).filter (wye node1166)).length = 4 := by decide +kernel
theorem census_node1167 : ((verts node1167).filter (wye node1167)).length = 5 := by decide +kernel
theorem arc_count291 : (entries291.map (fun g => ((verts g).filter (wye g)).length)).sum = 18 := by
  simp only [entries291, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1164, census_node1165, census_node1166, census_node1167]
  decide +kernel
end RawCert
