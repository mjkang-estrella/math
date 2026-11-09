import Closure187
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node752 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower752 : ∀ h, Pure node752 h → 11 ≤ h.length := by
  apply indexed_extend node752 [(2, node151), (5, node197)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower151
  · exact lower197
def node753 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 0, 1, 0], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower753 : ∀ h, Pure node753 h → 11 ≤ h.length := by
  apply indexed_extend node753 [(4, node190), (7, node196), (10, node235)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower190
  · exact lower196
  · exact lower235
def node754 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 2, 0, 0, 0, 1, 0, 1, 0]]
theorem lower754 : ∀ h, Pure node754 h → 11 ≤ h.length := by
  apply indexed_extend node754 [(7, node197), (10, node236)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower197
  · exact lower236
def node755 : Graph := [[0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0]]
theorem lower755 : ∀ h, Pure node755 h → 11 ≤ h.length := by
  apply indexed_extend node755 [(2, node152), (10, node238)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower152
  · exact lower238
def entries188 : List Graph := [node752, node753, node754, node755]
theorem entries_count188 : entries188.length = 4 := by decide +kernel
theorem census_node752 : ((verts node752).filter (wye node752)).length = 2 := by decide +kernel
theorem census_node753 : ((verts node753).filter (wye node753)).length = 3 := by decide +kernel
theorem census_node754 : ((verts node754).filter (wye node754)).length = 2 := by decide +kernel
theorem census_node755 : ((verts node755).filter (wye node755)).length = 2 := by decide +kernel
theorem arc_count188 : (entries188.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries188, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node752, census_node753, census_node754, census_node755]
  decide +kernel
end RawCert
