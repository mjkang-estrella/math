import Closure425
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1704 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 2], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1704 : ∀ h, Pure node1704 h → 11 ≤ h.length := by
  apply indexed_extend node1704 [(1, node439), (3, node921), (6, node913), (11, node909)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower439
  · exact lower921
  · exact lower913
  · exact lower909
def node1705 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 1, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1705 : ∀ h, Pure node1705 h → 11 ≤ h.length := by
  apply indexed_extend node1705 [(1, node440), (3, node922), (7, node915), (11, node910)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower440
  · exact lower922
  · exact lower915
  · exact lower910
def node1706 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1706 : ∀ h, Pure node1706 h → 11 ≤ h.length := by
  apply indexed_extend node1706 [(1, node443), (3, node923), (9, node913), (11, node912), (12, node964), (13, node911)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower443
  · exact lower923
  · exact lower913
  · exact lower912
  · exact lower964
  · exact lower911
def node1707 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 2, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1707 : ∀ h, Pure node1707 h → 11 ≤ h.length := by
  apply indexed_extend node1707 [(1, node448), (3, node924), (9, node915), (11, node914), (12, node965)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower448
  · exact lower924
  · exact lower915
  · exact lower914
  · exact lower965
def entries426 : List Graph := [node1704, node1705, node1706, node1707]
theorem entries_count426 : entries426.length = 4 := by decide +kernel
theorem census_node1704 : ((verts node1704).filter (wye node1704)).length = 4 := by decide +kernel
theorem census_node1705 : ((verts node1705).filter (wye node1705)).length = 4 := by decide +kernel
theorem census_node1706 : ((verts node1706).filter (wye node1706)).length = 6 := by decide +kernel
theorem census_node1707 : ((verts node1707).filter (wye node1707)).length = 5 := by decide +kernel
theorem arc_count426 : (entries426.map (fun g => ((verts g).filter (wye g)).length)).sum = 19 := by
  simp only [entries426, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1704, census_node1705, census_node1706, census_node1707]
  decide +kernel
end RawCert
