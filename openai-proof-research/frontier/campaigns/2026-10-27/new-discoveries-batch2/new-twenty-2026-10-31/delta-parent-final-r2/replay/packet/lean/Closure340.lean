import Closure339
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1360 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 2, 0]]
theorem lower1360 : ∀ h, Pure node1360 h → 11 ≤ h.length := by
  apply indexed_extend node1360 [(5, node614), (6, node590), (7, node591), (10, node579)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower614
  · exact lower590
  · exact lower591
  · exact lower579
def node1361 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0]]
theorem lower1361 : ∀ h, Pure node1361 h → 11 ≤ h.length := by
  apply indexed_extend node1361 [(4, node638), (6, node592), (8, node597), (10, node581)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower638
  · exact lower592
  · exact lower597
  · exact lower581
def node1362 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0], [2, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0]]
theorem lower1362 : ∀ h, Pure node1362 h → 11 ≤ h.length := by
  apply indexed_extend node1362 [(4, node639), (7, node594), (10, node582), (12, node579), (13, node578)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower639
  · exact lower594
  · exact lower582
  · exact lower579
  · exact lower578
def node1363 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0]]
theorem lower1363 : ∀ h, Pure node1363 h → 11 ≤ h.length := by
  apply indexed_extend node1363 [(5, node618), (6, node593), (7, node595), (10, node582), (13, node580)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower618
  · exact lower593
  · exact lower595
  · exact lower582
  · exact lower580
def entries340 : List Graph := [node1360, node1361, node1362, node1363]
theorem entries_count340 : entries340.length = 4 := by decide +kernel
theorem census_node1360 : ((verts node1360).filter (wye node1360)).length = 4 := by decide +kernel
theorem census_node1361 : ((verts node1361).filter (wye node1361)).length = 4 := by decide +kernel
theorem census_node1362 : ((verts node1362).filter (wye node1362)).length = 5 := by decide +kernel
theorem census_node1363 : ((verts node1363).filter (wye node1363)).length = 5 := by decide +kernel
theorem arc_count340 : (entries340.map (fun g => ((verts g).filter (wye g)).length)).sum = 18 := by
  simp only [entries340, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1360, census_node1361, census_node1362, census_node1363]
  decide +kernel
end RawCert
