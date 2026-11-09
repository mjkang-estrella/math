import Closure338
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1356 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower1356 : ∀ h, Pure node1356 h → 11 ≤ h.length := by
  apply indexed_extend node1356 [(1, node827), (7, node584), (12, node579)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower827
  · exact lower584
  · exact lower579
def node1357 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [2, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 2], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0]]
theorem lower1357 : ∀ h, Pure node1357 h → 11 ≤ h.length := by
  apply indexed_extend node1357 [(1, node828), (7, node585), (12, node582), (13, node577)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower828
  · exact lower585
  · exact lower582
  · exact lower577
def node1358 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower1358 : ∀ h, Pure node1358 h → 11 ≤ h.length := by
  apply indexed_extend node1358 [(1, node832), (2, node830), (7, node586), (8, node588)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower832
  · exact lower830
  · exact lower586
  · exact lower588
def node1359 : Graph := [[0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower1359 : ∀ h, Pure node1359 h → 11 ≤ h.length := by
  apply indexed_extend node1359 [(4, node638), (5, node613), (6, node589), (10, node578), (11, node580)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower638
  · exact lower613
  · exact lower589
  · exact lower578
  · exact lower580
def entries339 : List Graph := [node1356, node1357, node1358, node1359]
theorem entries_count339 : entries339.length = 4 := by decide +kernel
theorem census_node1356 : ((verts node1356).filter (wye node1356)).length = 3 := by decide +kernel
theorem census_node1357 : ((verts node1357).filter (wye node1357)).length = 4 := by decide +kernel
theorem census_node1358 : ((verts node1358).filter (wye node1358)).length = 4 := by decide +kernel
theorem census_node1359 : ((verts node1359).filter (wye node1359)).length = 5 := by decide +kernel
theorem arc_count339 : (entries339.map (fun g => ((verts g).filter (wye g)).length)).sum = 16 := by
  simp only [entries339, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1356, census_node1357, census_node1358, census_node1359]
  decide +kernel
end RawCert
