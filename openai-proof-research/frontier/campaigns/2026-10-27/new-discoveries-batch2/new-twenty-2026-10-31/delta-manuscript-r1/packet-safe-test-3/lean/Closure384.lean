import Closure383
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1536 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 1, 0]]
theorem lower1536 : ∀ h, Pure node1536 h → 11 ≤ h.length := by
  apply indexed_extend node1536 [(2, node656), (5, node754), (6, node755), (8, node752), (11, node856)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower656
  · exact lower754
  · exact lower755
  · exact lower752
  · exact lower856
def node1537 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1537 : ∀ h, Pure node1537 h → 11 ≤ h.length := by
  apply indexed_extend node1537 [(2, node657), (5, node757), (6, node758), (8, node756), (10, node854)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower657
  · exact lower757
  · exact lower758
  · exact lower756
  · exact lower854
def node1538 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1538 : ∀ h, Pure node1538 h → 11 ≤ h.length := by
  apply indexed_extend node1538 [(2, node658), (5, node760), (6, node761), (8, node759), (10, node857)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower658
  · exact lower760
  · exact lower761
  · exact lower759
  · exact lower857
def node1539 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1539 : ∀ h, Pure node1539 h → 11 ≤ h.length := by
  apply indexed_extend node1539 [(2, node678), (4, node764), (7, node762), (9, node744), (11, node858)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower678
  · exact lower764
  · exact lower762
  · exact lower744
  · exact lower858
def entries384 : List Graph := [node1536, node1537, node1538, node1539]
theorem entries_count384 : entries384.length = 4 := by decide +kernel
theorem census_node1536 : ((verts node1536).filter (wye node1536)).length = 5 := by decide +kernel
theorem census_node1537 : ((verts node1537).filter (wye node1537)).length = 5 := by decide +kernel
theorem census_node1538 : ((verts node1538).filter (wye node1538)).length = 5 := by decide +kernel
theorem census_node1539 : ((verts node1539).filter (wye node1539)).length = 5 := by decide +kernel
theorem arc_count384 : (entries384.map (fun g => ((verts g).filter (wye g)).length)).sum = 20 := by
  simp only [entries384, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1536, census_node1537, census_node1538, census_node1539]
  decide +kernel
end RawCert
