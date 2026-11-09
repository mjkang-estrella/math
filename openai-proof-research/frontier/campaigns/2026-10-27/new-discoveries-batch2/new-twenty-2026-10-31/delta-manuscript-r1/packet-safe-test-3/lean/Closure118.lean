import Closure117
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node472 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 1], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 2, 0, 0]]
theorem lower472 : ∀ h, Pure node472 h → 11 ≤ h.length := by
  apply indexed_extend node472 [(0, node266), (3, node42), (11, node121)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower266
  · exact lower42
  · exact lower121
def node473 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0]]
theorem lower473 : ∀ h, Pure node473 h → 11 ≤ h.length := by
  apply indexed_extend node473 [(0, node269), (4, node116), (7, node90)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower269
  · exact lower116
  · exact lower90
def node474 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0], [0, 0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0]]
theorem lower474 : ∀ h, Pure node474 h → 11 ≤ h.length := by
  apply indexed_extend node474 [(0, node278), (7, node90), (11, node125)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower278
  · exact lower90
  · exact lower125
def node475 : Graph := [[0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3], [0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0]]
theorem lower475 : ∀ h, Pure node475 h → 11 ≤ h.length := by
  apply indexed_extend node475 [(0, node279), (3, node43), (6, node90)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower279
  · exact lower43
  · exact lower90
def entries118 : List Graph := [node472, node473, node474, node475]
theorem entries_count118 : entries118.length = 4 := by decide +kernel
theorem census_node472 : ((verts node472).filter (wye node472)).length = 3 := by decide +kernel
theorem census_node473 : ((verts node473).filter (wye node473)).length = 3 := by decide +kernel
theorem census_node474 : ((verts node474).filter (wye node474)).length = 3 := by decide +kernel
theorem census_node475 : ((verts node475).filter (wye node475)).length = 3 := by decide +kernel
theorem arc_count118 : (entries118.map (fun g => ((verts g).filter (wye g)).length)).sum = 12 := by
  simp only [entries118, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node472, census_node473, census_node474, census_node475]
  decide +kernel
end RawCert
