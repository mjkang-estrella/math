import Closure287
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1152 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 1, 0, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1152 : ∀ h, Pure node1152 h → 11 ≤ h.length := by
  apply indexed_extend node1152 [(2, node695), (3, node295), (8, node455), (9, node454), (11, node453), (13, node450)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lower695
  · exact lower295
  · exact lower455
  · exact lower454
  · exact lower453
  · exact lower450
def node1153 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 2, 0, 0, 0]]
theorem lower1153 : ∀ h, Pure node1153 h → 11 ≤ h.length := by
  apply indexed_extend node1153 [(3, node293), (8, node457), (10, node456)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower293
  · exact lower457
  · exact lower456
def node1154 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower1154 : ∀ h, Pure node1154 h → 11 ≤ h.length := by
  apply indexed_extend node1154 [(2, node696), (8, node458), (9, node459), (11, node456)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower696
  · exact lower458
  · exact lower459
  · exact lower456
def node1155 : Graph := [[0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1], [1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1155 : ∀ h, Pure node1155 h → 11 ≤ h.length := by
  apply indexed_extend node1155 [(2, node697), (3, node296), (8, node460), (9, node458), (11, node457)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower697
  · exact lower296
  · exact lower460
  · exact lower458
  · exact lower457
def entries288 : List Graph := [node1152, node1153, node1154, node1155]
theorem entries_count288 : entries288.length = 4 := by decide +kernel
theorem census_node1152 : ((verts node1152).filter (wye node1152)).length = 6 := by decide +kernel
theorem census_node1153 : ((verts node1153).filter (wye node1153)).length = 3 := by decide +kernel
theorem census_node1154 : ((verts node1154).filter (wye node1154)).length = 4 := by decide +kernel
theorem census_node1155 : ((verts node1155).filter (wye node1155)).length = 5 := by decide +kernel
theorem arc_count288 : (entries288.map (fun g => ((verts g).filter (wye g)).length)).sum = 18 := by
  simp only [entries288, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1152, census_node1153, census_node1154, census_node1155]
  decide +kernel
end RawCert
