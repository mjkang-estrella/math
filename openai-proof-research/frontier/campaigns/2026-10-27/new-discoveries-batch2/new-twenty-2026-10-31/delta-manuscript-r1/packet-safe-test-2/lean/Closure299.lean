import Closure298
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1196 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower1196 : ∀ h, Pure node1196 h → 11 ≤ h.length := by
  apply indexed_extend node1196 [(0, node943), (5, node527), (8, node471), (12, node590)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower943
  · exact lower527
  · exact lower471
  · exact lower590
def node1197 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 1], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 0]]
theorem lower1197 : ∀ h, Pure node1197 h → 11 ≤ h.length := by
  apply indexed_extend node1197 [(0, node944), (3, node326), (5, node528), (9, node472), (12, node591)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower944
  · exact lower326
  · exact lower528
  · exact lower472
  · exact lower591
def node1198 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0]]
theorem lower1198 : ∀ h, Pure node1198 h → 11 ≤ h.length := by
  apply indexed_extend node1198 [(0, node946), (4, node556), (7, node474), (8, node473), (12, node592)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower946
  · exact lower556
  · exact lower474
  · exact lower473
  · exact lower592
def node1199 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0]]
theorem lower1199 : ∀ h, Pure node1199 h → 11 ≤ h.length := by
  apply indexed_extend node1199 [(0, node966), (3, node327), (6, node474), (8, node475), (9, node476), (12, node597)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower966
  · exact lower327
  · exact lower474
  · exact lower475
  · exact lower476
  · exact lower597
def entries299 : List Graph := [node1196, node1197, node1198, node1199]
theorem entries_count299 : entries299.length = 4 := by decide +kernel
theorem census_node1196 : ((verts node1196).filter (wye node1196)).length = 4 := by decide +kernel
theorem census_node1197 : ((verts node1197).filter (wye node1197)).length = 5 := by decide +kernel
theorem census_node1198 : ((verts node1198).filter (wye node1198)).length = 5 := by decide +kernel
theorem census_node1199 : ((verts node1199).filter (wye node1199)).length = 6 := by decide +kernel
theorem arc_count299 : (entries299.map (fun g => ((verts g).filter (wye g)).length)).sum = 20 := by
  simp only [entries299, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1196, census_node1197, census_node1198, census_node1199]
  decide +kernel
end RawCert
