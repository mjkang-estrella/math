import Closure280
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1124 : Graph := [[0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1124 : ∀ h, Pure node1124 h → 11 ≤ h.length := by
  apply indexed_extend node1124 [(1, node678), (7, node422), (9, node420), (13, node418)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower678
  · exact lower422
  · exact lower420
  · exact lower418
def node1125 : Graph := [[0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0]]
theorem lower1125 : ∀ h, Pure node1125 h → 11 ≤ h.length := by
  apply indexed_extend node1125 [(1, node679), (5, node424), (7, node423), (12, node419)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower679
  · exact lower424
  · exact lower423
  · exact lower419
def node1126 : Graph := [[0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1126 : ∀ h, Pure node1126 h → 11 ≤ h.length := by
  apply indexed_extend node1126 [(5, node426), (7, node425), (9, node421), (12, node419), (13, node418)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower426
  · exact lower425
  · exact lower421
  · exact lower419
  · exact lower418
def node1127 : Graph := [[0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1127 : ∀ h, Pure node1127 h → 11 ≤ h.length := by
  apply indexed_extend node1127 [(1, node680), (5, node428), (7, node427), (12, node421), (13, node420)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower680
  · exact lower428
  · exact lower427
  · exact lower421
  · exact lower420
def entries281 : List Graph := [node1124, node1125, node1126, node1127]
theorem entries_count281 : entries281.length = 4 := by decide +kernel
theorem census_node1124 : ((verts node1124).filter (wye node1124)).length = 4 := by decide +kernel
theorem census_node1125 : ((verts node1125).filter (wye node1125)).length = 4 := by decide +kernel
theorem census_node1126 : ((verts node1126).filter (wye node1126)).length = 5 := by decide +kernel
theorem census_node1127 : ((verts node1127).filter (wye node1127)).length = 5 := by decide +kernel
theorem arc_count281 : (entries281.map (fun g => ((verts g).filter (wye g)).length)).sum = 18 := by
  simp only [entries281, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1124, census_node1125, census_node1126, census_node1127]
  decide +kernel
end RawCert
