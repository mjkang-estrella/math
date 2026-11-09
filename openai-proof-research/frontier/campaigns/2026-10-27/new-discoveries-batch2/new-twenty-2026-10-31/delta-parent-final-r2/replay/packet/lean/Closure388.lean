import Closure387
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1552 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 0, 0]]
theorem lower1552 : ∀ h, Pure node1552 h → 11 ≤ h.length := by
  apply indexed_extend node1552 [(2, node666), (4, node766), (10, node755), (11, node876)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower666
  · exact lower766
  · exact lower755
  · exact lower876
def node1553 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1553 : ∀ h, Pure node1553 h → 11 ≤ h.length := by
  apply indexed_extend node1553 [(2, node680), (4, node777), (5, node778), (7, node776), (10, node860), (13, node744)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower680
  · exact lower777
  · exact lower778
  · exact lower776
  · exact lower860
  · exact lower744
def node1554 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1554 : ∀ h, Pure node1554 h → 11 ≤ h.length := by
  apply indexed_extend node1554 [(2, node667), (5, node779), (7, node783), (9, node756), (11, node746)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower667
  · exact lower779
  · exact lower783
  · exact lower756
  · exact lower746
def node1555 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1555 : ∀ h, Pure node1555 h → 11 ≤ h.length := by
  apply indexed_extend node1555 [(2, node668), (5, node780), (9, node756), (13, node745)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower668
  · exact lower780
  · exact lower756
  · exact lower745
def entries388 : List Graph := [node1552, node1553, node1554, node1555]
theorem entries_count388 : entries388.length = 4 := by decide +kernel
theorem census_node1552 : ((verts node1552).filter (wye node1552)).length = 4 := by decide +kernel
theorem census_node1553 : ((verts node1553).filter (wye node1553)).length = 6 := by decide +kernel
theorem census_node1554 : ((verts node1554).filter (wye node1554)).length = 5 := by decide +kernel
theorem census_node1555 : ((verts node1555).filter (wye node1555)).length = 4 := by decide +kernel
theorem arc_count388 : (entries388.map (fun g => ((verts g).filter (wye g)).length)).sum = 19 := by
  simp only [entries388, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1552, census_node1553, census_node1554, census_node1555]
  decide +kernel
end RawCert
