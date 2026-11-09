import Closure345
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1384 : Graph := [[0, 0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0]]
theorem lower1384 : ∀ h, Pure node1384 h → 11 ≤ h.length := by
  apply indexed_extend node1384 [(2, node851), (8, node602), (10, node601), (12, node604)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower851
  · exact lower602
  · exact lower601
  · exact lower604
def node1385 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1, 0], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower1385 : ∀ h, Pure node1385 h → 11 ≤ h.length := by
  apply indexed_extend node1385 [(1, node855), (2, node852), (5, node606), (6, node607), (13, node605)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower855
  · exact lower852
  · exact lower606
  · exact lower607
  · exact lower605
def node1386 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 1, 0]]
theorem lower1386 : ∀ h, Pure node1386 h → 11 ≤ h.length := by
  apply indexed_extend node1386 [(1, node856), (2, node853), (6, node608), (7, node610), (8, node612)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower856
  · exact lower853
  · exact lower608
  · exact lower610
  · exact lower612
def node1387 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1387 : ∀ h, Pure node1387 h → 11 ≤ h.length := by
  apply indexed_extend node1387 [(1, node857), (2, node854), (6, node609), (7, node611)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower857
  · exact lower854
  · exact lower609
  · exact lower611
def entries346 : List Graph := [node1384, node1385, node1386, node1387]
theorem entries_count346 : entries346.length = 4 := by decide +kernel
theorem census_node1384 : ((verts node1384).filter (wye node1384)).length = 4 := by decide +kernel
theorem census_node1385 : ((verts node1385).filter (wye node1385)).length = 5 := by decide +kernel
theorem census_node1386 : ((verts node1386).filter (wye node1386)).length = 5 := by decide +kernel
theorem census_node1387 : ((verts node1387).filter (wye node1387)).length = 4 := by decide +kernel
theorem arc_count346 : (entries346.map (fun g => ((verts g).filter (wye g)).length)).sum = 18 := by
  simp only [entries346, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1384, census_node1385, census_node1386, census_node1387]
  decide +kernel
end RawCert
