import Closure391
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1568 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1568 : ∀ h, Pure node1568 h → 11 ≤ h.length := by
  apply indexed_extend node1568 [(6, node786), (8, node777), (10, node878), (11, node765), (13, node764)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower786
  · exact lower777
  · exact lower878
  · exact lower765
  · exact lower764
def node1569 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1], [1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1569 : ∀ h, Pure node1569 h → 11 ≤ h.length := by
  apply indexed_extend node1569 [(2, node682), (8, node778), (10, node879), (11, node766)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower682
  · exact lower778
  · exact lower879
  · exact lower766
def node1570 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1570 : ∀ h, Pure node1570 h → 11 ≤ h.length := by
  apply indexed_extend node1570 [(6, node787), (8, node780), (9, node779), (11, node768), (13, node767)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower787
  · exact lower780
  · exact lower779
  · exact lower768
  · exact lower767
def node1571 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1571 : ∀ h, Pure node1571 h → 11 ≤ h.length := by
  apply indexed_extend node1571 [(6, node787), (9, node781), (10, node880), (11, node771), (13, node769)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower787
  · exact lower781
  · exact lower880
  · exact lower771
  · exact lower769
def entries392 : List Graph := [node1568, node1569, node1570, node1571]
theorem entries_count392 : entries392.length = 4 := by decide +kernel
theorem census_node1568 : ((verts node1568).filter (wye node1568)).length = 5 := by decide +kernel
theorem census_node1569 : ((verts node1569).filter (wye node1569)).length = 4 := by decide +kernel
theorem census_node1570 : ((verts node1570).filter (wye node1570)).length = 5 := by decide +kernel
theorem census_node1571 : ((verts node1571).filter (wye node1571)).length = 5 := by decide +kernel
theorem arc_count392 : (entries392.map (fun g => ((verts g).filter (wye g)).length)).sum = 19 := by
  simp only [entries392, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1568, census_node1569, census_node1570, census_node1571]
  decide +kernel
end RawCert
