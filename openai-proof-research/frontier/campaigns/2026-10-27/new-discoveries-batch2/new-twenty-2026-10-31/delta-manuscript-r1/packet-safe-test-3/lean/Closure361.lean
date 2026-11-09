import Closure360
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1444 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1444 : ∀ h, Pure node1444 h → 11 ≤ h.length := by
  apply indexed_extend node1444 [(0, node379), (2, node328), (5, node745), (6, node698)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower379
  · exact lower328
  · exact lower745
  · exact lower698
def node1445 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 0], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1445 : ∀ h, Pure node1445 h → 11 ≤ h.length := by
  apply indexed_extend node1445 [(0, node380), (2, node329), (11, node793)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower380
  · exact lower329
  · exact lower793
def node1446 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower1446 : ∀ h, Pure node1446 h → 11 ≤ h.length := by
  apply indexed_extend node1446 [(0, node381), (2, node330), (5, node746), (6, node699), (8, node703)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower381
  · exact lower330
  · exact lower746
  · exact lower699
  · exact lower703
def node1447 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower1447 : ∀ h, Pure node1447 h → 11 ≤ h.length := by
  apply indexed_extend node1447 [(0, node382), (2, node331), (7, node700), (8, node704), (11, node794)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower382
  · exact lower331
  · exact lower700
  · exact lower704
  · exact lower794
def entries361 : List Graph := [node1444, node1445, node1446, node1447]
theorem entries_count361 : entries361.length = 4 := by decide +kernel
theorem census_node1444 : ((verts node1444).filter (wye node1444)).length = 4 := by decide +kernel
theorem census_node1445 : ((verts node1445).filter (wye node1445)).length = 3 := by decide +kernel
theorem census_node1446 : ((verts node1446).filter (wye node1446)).length = 5 := by decide +kernel
theorem census_node1447 : ((verts node1447).filter (wye node1447)).length = 5 := by decide +kernel
theorem arc_count361 : (entries361.map (fun g => ((verts g).filter (wye g)).length)).sum = 17 := by
  simp only [entries361, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1444, census_node1445, census_node1446, census_node1447]
  decide +kernel
end RawCert
