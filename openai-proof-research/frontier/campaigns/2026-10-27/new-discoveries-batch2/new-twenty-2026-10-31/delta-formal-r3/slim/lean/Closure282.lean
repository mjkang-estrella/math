import Closure281
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1128 : Graph := [[0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1128 : ∀ h, Pure node1128 h → 11 ≤ h.length := by
  apply indexed_extend node1128 [(1, node681), (8, node427), (11, node423), (12, node425), (13, node422)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower681
  · exact lower427
  · exact lower423
  · exact lower425
  · exact lower422
def node1129 : Graph := [[0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1], [1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1129 : ∀ h, Pure node1129 h → 11 ≤ h.length := by
  apply indexed_extend node1129 [(1, node682), (8, node428), (11, node424), (12, node426)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower682
  · exact lower428
  · exact lower424
  · exact lower426
def node1130 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1130 : ∀ h, Pure node1130 h → 11 ≤ h.length := by
  apply indexed_extend node1130 [(2, node683), (5, node430), (7, node431), (8, node432)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower683
  · exact lower430
  · exact lower431
  · exact lower432
def node1131 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower1131 : ∀ h, Pure node1131 h → 11 ≤ h.length := by
  apply indexed_extend node1131 [(5, node433), (6, node435), (7, node436), (8, node437), (10, node429)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower433
  · exact lower435
  · exact lower436
  · exact lower437
  · exact lower429
def entries282 : List Graph := [node1128, node1129, node1130, node1131]
theorem entries_count282 : entries282.length = 4 := by decide +kernel
theorem census_node1128 : ((verts node1128).filter (wye node1128)).length = 5 := by decide +kernel
theorem census_node1129 : ((verts node1129).filter (wye node1129)).length = 4 := by decide +kernel
theorem census_node1130 : ((verts node1130).filter (wye node1130)).length = 4 := by decide +kernel
theorem census_node1131 : ((verts node1131).filter (wye node1131)).length = 5 := by decide +kernel
theorem arc_count282 : (entries282.map (fun g => ((verts g).filter (wye g)).length)).sum = 18 := by
  simp only [entries282, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1128, census_node1129, census_node1130, census_node1131]
  decide +kernel
end RawCert
