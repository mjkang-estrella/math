import Closure283
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1136 : Graph := [[0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1136 : ∀ h, Pure node1136 h → 11 ≤ h.length := by
  apply indexed_extend node1136 [(2, node688), (6, node448), (9, node440), (11, node437), (13, node432)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower688
  · exact lower448
  · exact lower440
  · exact lower437
  · exact lower432
def node1137 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower1137 : ∀ h, Pure node1137 h → 11 ≤ h.length := by
  apply indexed_extend node1137 [(2, node689), (3, node283), (5, node450), (9, node441)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower689
  · exact lower283
  · exact lower450
  · exact lower441
def node1138 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0], [0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower1138 : ∀ h, Pure node1138 h → 11 ≤ h.length := by
  apply indexed_extend node1138 [(2, node690), (3, node284), (9, node442)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower690
  · exact lower284
  · exact lower442
def node1139 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower1139 : ∀ h, Pure node1139 h → 11 ≤ h.length := by
  apply indexed_extend node1139 [(3, node285), (5, node449), (8, node441), (9, node442)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower285
  · exact lower449
  · exact lower441
  · exact lower442
def entries284 : List Graph := [node1136, node1137, node1138, node1139]
theorem entries_count284 : entries284.length = 4 := by decide +kernel
theorem census_node1136 : ((verts node1136).filter (wye node1136)).length = 5 := by decide +kernel
theorem census_node1137 : ((verts node1137).filter (wye node1137)).length = 4 := by decide +kernel
theorem census_node1138 : ((verts node1138).filter (wye node1138)).length = 3 := by decide +kernel
theorem census_node1139 : ((verts node1139).filter (wye node1139)).length = 4 := by decide +kernel
theorem arc_count284 : (entries284.map (fun g => ((verts g).filter (wye g)).length)).sum = 16 := by
  simp only [entries284, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1136, census_node1137, census_node1138, census_node1139]
  decide +kernel
end RawCert
