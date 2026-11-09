import Closure386
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1548 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower1548 : ∀ h, Pure node1548 h → 11 ≤ h.length := by
  apply indexed_extend node1548 [(2, node664), (4, node762), (5, node774), (9, node751)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower664
  · exact lower762
  · exact lower774
  · exact lower751
def node1549 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower1549 : ∀ h, Pure node1549 h → 11 ≤ h.length := by
  apply indexed_extend node1549 [(2, node665), (4, node763), (5, node775), (10, node752)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower665
  · exact lower763
  · exact lower775
  · exact lower752
def node1550 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1550 : ∀ h, Pure node1550 h → 11 ≤ h.length := by
  apply indexed_extend node1550 [(4, node764), (7, node774), (9, node753), (11, node871)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower764
  · exact lower774
  · exact lower753
  · exact lower871
def node1551 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0]]
theorem lower1551 : ∀ h, Pure node1551 h → 11 ≤ h.length := by
  apply indexed_extend node1551 [(4, node765), (7, node775), (10, node754), (11, node873)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower765
  · exact lower775
  · exact lower754
  · exact lower873
def entries387 : List Graph := [node1548, node1549, node1550, node1551]
theorem entries_count387 : entries387.length = 4 := by decide +kernel
theorem census_node1548 : ((verts node1548).filter (wye node1548)).length = 4 := by decide +kernel
theorem census_node1549 : ((verts node1549).filter (wye node1549)).length = 4 := by decide +kernel
theorem census_node1550 : ((verts node1550).filter (wye node1550)).length = 4 := by decide +kernel
theorem census_node1551 : ((verts node1551).filter (wye node1551)).length = 4 := by decide +kernel
theorem arc_count387 : (entries387.map (fun g => ((verts g).filter (wye g)).length)).sum = 16 := by
  simp only [entries387, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1548, census_node1549, census_node1550, census_node1551]
  decide +kernel
end RawCert
