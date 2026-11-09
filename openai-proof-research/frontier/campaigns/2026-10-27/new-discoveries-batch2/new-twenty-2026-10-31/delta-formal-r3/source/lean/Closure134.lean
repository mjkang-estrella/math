import Closure133
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node536 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 2, 0, 0, 1, 0, 1, 0]]
theorem lower536 : ∀ h, Pure node536 h → 11 ≤ h.length := by
  apply indexed_extend node536 [(1, node197), (2, node192), (7, node114)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower197
  · exact lower192
  · exact lower114
def node537 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 1, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 1, 1, 0, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower537 : ∀ h, Pure node537 h → 11 ≤ h.length := by
  apply indexed_extend node537 [(1, node190), (7, node113), (10, node129), (12, node101)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower190
  · exact lower113
  · exact lower129
  · exact lower101
def node538 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0], [1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 2, 0, 0, 1, 0, 1, 0]]
theorem lower538 : ∀ h, Pure node538 h → 11 ≤ h.length := by
  apply indexed_extend node538 [(2, node193), (7, node114), (10, node130)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower193
  · exact lower114
  · exact lower130
def node539 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 1], [1, 0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0]]
theorem lower539 : ∀ h, Pure node539 h → 11 ≤ h.length := by
  apply indexed_extend node539 [(2, node194), (3, node66), (10, node131)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower194
  · exact lower66
  · exact lower131
def entries134 : List Graph := [node536, node537, node538, node539]
theorem entries_count134 : entries134.length = 4 := by decide +kernel
theorem census_node536 : ((verts node536).filter (wye node536)).length = 3 := by decide +kernel
theorem census_node537 : ((verts node537).filter (wye node537)).length = 4 := by decide +kernel
theorem census_node538 : ((verts node538).filter (wye node538)).length = 3 := by decide +kernel
theorem census_node539 : ((verts node539).filter (wye node539)).length = 3 := by decide +kernel
theorem arc_count134 : (entries134.map (fun g => ((verts g).filter (wye g)).length)).sum = 13 := by
  simp only [entries134, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node536, census_node537, census_node538, census_node539]
  decide +kernel
end RawCert
