import Closure418
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1676 : Graph := [[0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1676 : ∀ h, Pure node1676 h → 11 ≤ h.length := by
  apply indexed_extend node1676 [(0, node692), (1, node647), (6, node903), (7, node922)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower692
  · exact lower647
  · exact lower903
  · exact lower922
def node1677 : Graph := [[0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1677 : ∀ h, Pure node1677 h → 11 ≤ h.length := by
  apply indexed_extend node1677 [(0, node290), (3, node904), (7, node894), (9, node893), (13, node942)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower290
  · exact lower904
  · exact lower894
  · exact lower893
  · exact lower942
def node1678 : Graph := [[0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 3, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1678 : ∀ h, Pure node1678 h → 11 ≤ h.length := by
  apply indexed_extend node1678 [(0, node291), (4, node904), (7, node895), (8, node896), (13, node945)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower291
  · exact lower904
  · exact lower895
  · exact lower896
  · exact lower945
def node1679 : Graph := [[0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1679 : ∀ h, Pure node1679 h → 11 ≤ h.length := by
  apply indexed_extend node1679 [(0, node693), (1, node648), (3, node904), (6, node916), (7, node897), (13, node946)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower693
  · exact lower648
  · exact lower904
  · exact lower916
  · exact lower897
  · exact lower946
def entries419 : List Graph := [node1676, node1677, node1678, node1679]
theorem entries_count419 : entries419.length = 4 := by decide +kernel
theorem census_node1676 : ((verts node1676).filter (wye node1676)).length = 4 := by decide +kernel
theorem census_node1677 : ((verts node1677).filter (wye node1677)).length = 5 := by decide +kernel
theorem census_node1678 : ((verts node1678).filter (wye node1678)).length = 5 := by decide +kernel
theorem census_node1679 : ((verts node1679).filter (wye node1679)).length = 6 := by decide +kernel
theorem arc_count419 : (entries419.map (fun g => ((verts g).filter (wye g)).length)).sum = 20 := by
  simp only [entries419, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1676, census_node1677, census_node1678, census_node1679]
  decide +kernel
end RawCert
