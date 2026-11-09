import Closure422
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1692 : Graph := [[0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1692 : ∀ h, Pure node1692 h → 11 ≤ h.length := by
  apply indexed_extend node1692 [(0, node317), (6, node905), (12, node955), (13, node904)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower317
  · exact lower905
  · exact lower955
  · exact lower904
def node1693 : Graph := [[0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1693 : ∀ h, Pure node1693 h → 11 ≤ h.length := by
  apply indexed_extend node1693 [(0, node318), (7, node906), (12, node956)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower318
  · exact lower906
  · exact lower956
def node1694 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower1694 : ∀ h, Pure node1694 h → 11 ≤ h.length := by
  apply indexed_extend node1694 [(1, node429), (6, node907), (7, node908), (8, node909), (9, node910)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower429
  · exact lower907
  · exact lower908
  · exact lower909
  · exact lower910
def node1695 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1695 : ∀ h, Pure node1695 h → 11 ≤ h.length := by
  apply indexed_extend node1695 [(1, node430), (3, node916), (7, node911), (13, node957)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower430
  · exact lower916
  · exact lower911
  · exact lower957
def entries423 : List Graph := [node1692, node1693, node1694, node1695]
theorem entries_count423 : entries423.length = 4 := by decide +kernel
theorem census_node1692 : ((verts node1692).filter (wye node1692)).length = 4 := by decide +kernel
theorem census_node1693 : ((verts node1693).filter (wye node1693)).length = 3 := by decide +kernel
theorem census_node1694 : ((verts node1694).filter (wye node1694)).length = 5 := by decide +kernel
theorem census_node1695 : ((verts node1695).filter (wye node1695)).length = 4 := by decide +kernel
theorem arc_count423 : (entries423.map (fun g => ((verts g).filter (wye g)).length)).sum = 16 := by
  simp only [entries423, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1692, census_node1693, census_node1694, census_node1695]
  decide +kernel
end RawCert
