import Closure325
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1304 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 2], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1304 : ∀ h, Pure node1304 h → 11 ≤ h.length := by
  apply indexed_extend node1304 [(2, node783), (3, node417), (6, node553), (11, node540)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower783
  · exact lower417
  · exact lower553
  · exact lower540
def node1305 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1305 : ∀ h, Pure node1305 h → 11 ≤ h.length := by
  apply indexed_extend node1305 [(1, node786), (8, node552), (11, node547), (12, node550), (13, node546)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower786
  · exact lower552
  · exact lower547
  · exact lower550
  · exact lower546
def node1306 : Graph := [[0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1306 : ∀ h, Pure node1306 h → 11 ≤ h.length := by
  apply indexed_extend node1306 [(2, node787), (9, node553), (11, node549), (12, node551), (13, node548)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower787
  · exact lower553
  · exact lower549
  · exact lower551
  · exact lower548
def node1307 : Graph := [[0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 0]]
theorem lower1307 : ∀ h, Pure node1307 h → 11 ≤ h.length := by
  apply indexed_extend node1307 [(0, node945), (3, node485), (5, node556), (8, node554), (9, node555), (12, node638)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower945
  · exact lower485
  · exact lower556
  · exact lower554
  · exact lower555
  · exact lower638
def entries326 : List Graph := [node1304, node1305, node1306, node1307]
theorem entries_count326 : entries326.length = 4 := by decide +kernel
theorem census_node1304 : ((verts node1304).filter (wye node1304)).length = 4 := by decide +kernel
theorem census_node1305 : ((verts node1305).filter (wye node1305)).length = 5 := by decide +kernel
theorem census_node1306 : ((verts node1306).filter (wye node1306)).length = 5 := by decide +kernel
theorem census_node1307 : ((verts node1307).filter (wye node1307)).length = 6 := by decide +kernel
theorem arc_count326 : (entries326.map (fun g => ((verts g).filter (wye g)).length)).sum = 20 := by
  simp only [entries326, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1304, census_node1305, census_node1306, census_node1307]
  decide +kernel
end RawCert
