import Closure315
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1264 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1264 : ∀ h, Pure node1264 h → 11 ≤ h.length := by
  apply indexed_extend node1264 [(1, node751), (2, node745), (3, node403), (5, node534), (6, node535), (13, node502)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower751
  · exact lower745
  · exact lower403
  · exact lower534
  · exact lower535
  · exact lower502
def node1265 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower1265 : ∀ h, Pure node1265 h → 11 ≤ h.length := by
  apply indexed_extend node1265 [(1, node752), (2, node746), (3, node404), (6, node536), (8, node540)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower752
  · exact lower746
  · exact lower404
  · exact lower536
  · exact lower540
def node1266 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1266 : ∀ h, Pure node1266 h → 11 ≤ h.length := by
  apply indexed_extend node1266 [(1, node744), (3, node420), (5, node537), (8, node534), (11, node606), (13, node503)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower744
  · exact lower420
  · exact lower537
  · exact lower534
  · exact lower606
  · exact lower503
def node1267 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 0, 1, 0], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1267 : ∀ h, Pure node1267 h → 11 ≤ h.length := by
  apply indexed_extend node1267 [(1, node753), (2, node747), (5, node537), (8, node535), (11, node607), (13, node504)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower753
  · exact lower747
  · exact lower537
  · exact lower535
  · exact lower607
  · exact lower504
def entries316 : List Graph := [node1264, node1265, node1266, node1267]
theorem entries_count316 : entries316.length = 4 := by decide +kernel
theorem census_node1264 : ((verts node1264).filter (wye node1264)).length = 6 := by decide +kernel
theorem census_node1265 : ((verts node1265).filter (wye node1265)).length = 5 := by decide +kernel
theorem census_node1266 : ((verts node1266).filter (wye node1266)).length = 6 := by decide +kernel
theorem census_node1267 : ((verts node1267).filter (wye node1267)).length = 6 := by decide +kernel
theorem arc_count316 : (entries316.map (fun g => ((verts g).filter (wye g)).length)).sum = 23 := by
  simp only [entries316, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1264, census_node1265, census_node1266, census_node1267]
  decide +kernel
end RawCert
