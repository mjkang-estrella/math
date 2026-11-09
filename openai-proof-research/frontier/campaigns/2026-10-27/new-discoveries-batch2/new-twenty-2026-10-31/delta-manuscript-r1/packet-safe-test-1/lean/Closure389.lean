import Closure388
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1556 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1556 : ∀ h, Pure node1556 h → 11 ≤ h.length := by
  apply indexed_extend node1556 [(6, node781), (7, node779), (9, node757), (10, node862), (11, node748)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower781
  · exact lower779
  · exact lower757
  · exact lower862
  · exact lower748
def node1557 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1557 : ∀ h, Pure node1557 h → 11 ≤ h.length := by
  apply indexed_extend node1557 [(7, node780), (9, node757), (10, node864), (13, node747)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower780
  · exact lower757
  · exact lower864
  · exact lower747
def node1558 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower1558 : ∀ h, Pure node1558 h → 11 ≤ h.length := by
  apply indexed_extend node1558 [(2, node669), (6, node782), (9, node758), (10, node865), (11, node749)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower669
  · exact lower782
  · exact lower758
  · exact lower865
  · exact lower749
def node1559 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1559 : ∀ h, Pure node1559 h → 11 ≤ h.length := by
  apply indexed_extend node1559 [(2, node670), (9, node758), (10, node867)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower670
  · exact lower758
  · exact lower867
def entries389 : List Graph := [node1556, node1557, node1558, node1559]
theorem entries_count389 : entries389.length = 4 := by decide +kernel
theorem census_node1556 : ((verts node1556).filter (wye node1556)).length = 5 := by decide +kernel
theorem census_node1557 : ((verts node1557).filter (wye node1557)).length = 4 := by decide +kernel
theorem census_node1558 : ((verts node1558).filter (wye node1558)).length = 5 := by decide +kernel
theorem census_node1559 : ((verts node1559).filter (wye node1559)).length = 3 := by decide +kernel
theorem arc_count389 : (entries389.map (fun g => ((verts g).filter (wye g)).length)).sum = 17 := by
  simp only [entries389, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1556, census_node1557, census_node1558, census_node1559]
  decide +kernel
end RawCert
