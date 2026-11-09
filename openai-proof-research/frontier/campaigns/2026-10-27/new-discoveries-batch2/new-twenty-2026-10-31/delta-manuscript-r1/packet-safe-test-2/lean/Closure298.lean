import Closure297
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1192 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0]]
theorem lower1192 : ∀ h, Pure node1192 h → 11 ≤ h.length := by
  apply indexed_extend node1192 [(0, node931), (3, node323), (5, node503), (6, node469), (9, node467), (10, node468), (12, node580)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower931
  · exact lower323
  · exact lower503
  · exact lower469
  · exact lower467
  · exact lower468
  · exact lower580
def node1193 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0]]
theorem lower1193 : ∀ h, Pure node1193 h → 11 ≤ h.length := by
  apply indexed_extend node1193 [(0, node936), (3, node324), (4, node554), (6, node473), (8, node475)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower936
  · exact lower324
  · exact lower554
  · exact lower473
  · exact lower475
def node1194 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0]]
theorem lower1194 : ∀ h, Pure node1194 h → 11 ≤ h.length := by
  apply indexed_extend node1194 [(0, node937), (3, node325), (4, node555), (8, node476), (12, node581)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower937
  · exact lower325
  · exact lower555
  · exact lower476
  · exact lower581
def node1195 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0]]
theorem lower1195 : ∀ h, Pure node1195 h → 11 ≤ h.length := by
  apply indexed_extend node1195 [(0, node942), (4, node556), (5, node526), (8, node470), (10, node469), (12, node589)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower942
  · exact lower556
  · exact lower526
  · exact lower470
  · exact lower469
  · exact lower589
def entries298 : List Graph := [node1192, node1193, node1194, node1195]
theorem entries_count298 : entries298.length = 4 := by decide +kernel
theorem census_node1192 : ((verts node1192).filter (wye node1192)).length = 7 := by decide +kernel
theorem census_node1193 : ((verts node1193).filter (wye node1193)).length = 5 := by decide +kernel
theorem census_node1194 : ((verts node1194).filter (wye node1194)).length = 5 := by decide +kernel
theorem census_node1195 : ((verts node1195).filter (wye node1195)).length = 6 := by decide +kernel
theorem arc_count298 : (entries298.map (fun g => ((verts g).filter (wye g)).length)).sum = 23 := by
  simp only [entries298, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1192, census_node1193, census_node1194, census_node1195]
  decide +kernel
end RawCert
