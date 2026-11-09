import Closure405
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1624 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1624 : ∀ h, Pure node1624 h → 11 ≤ h.length := by
  apply indexed_extend node1624 [(5, node847), (6, node848), (9, node832)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower847
  · exact lower848
  · exact lower832
def node1625 : Graph := [[0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [1, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower1625 : ∀ h, Pure node1625 h → 11 ≤ h.length := by
  apply indexed_extend node1625 [(3, node883), (6, node849), (10, node832), (13, node831)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower883
  · exact lower849
  · exact lower832
  · exact lower831
def node1626 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0]]
theorem lower1626 : ∀ h, Pure node1626 h → 11 ≤ h.length := by
  apply indexed_extend node1626 [(3, node884), (4, node878), (9, node836), (11, node834), (13, node833)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower884
  · exact lower878
  · exact lower836
  · exact lower834
  · exact lower833
def node1627 : Graph := [[0, 0, 3, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 2, 0, 0]]
theorem lower1627 : ∀ h, Pure node1627 h → 11 ≤ h.length := by
  apply indexed_extend node1627 [(3, node885), (4, node879), (8, node837), (9, node838), (11, node835)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower885
  · exact lower879
  · exact lower837
  · exact lower838
  · exact lower835
def entries406 : List Graph := [node1624, node1625, node1626, node1627]
theorem entries_count406 : entries406.length = 4 := by decide +kernel
theorem census_node1624 : ((verts node1624).filter (wye node1624)).length = 3 := by decide +kernel
theorem census_node1625 : ((verts node1625).filter (wye node1625)).length = 4 := by decide +kernel
theorem census_node1626 : ((verts node1626).filter (wye node1626)).length = 5 := by decide +kernel
theorem census_node1627 : ((verts node1627).filter (wye node1627)).length = 5 := by decide +kernel
theorem arc_count406 : (entries406.map (fun g => ((verts g).filter (wye g)).length)).sum = 17 := by
  simp only [entries406, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1624, census_node1625, census_node1626, census_node1627]
  decide +kernel
end RawCert
