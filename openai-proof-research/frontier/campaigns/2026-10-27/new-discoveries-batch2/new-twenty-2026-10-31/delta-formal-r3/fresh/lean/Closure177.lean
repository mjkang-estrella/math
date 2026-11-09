import Closure176
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node708 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower708 : ∀ h, Pure node708 h → 11 ≤ h.length := by
  apply indexed_extend node708 [(0, node84), (4, node182), (5, node196)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower84
  · exact lower182
  · exact lower196
def node709 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 1, 0, 0, 2, 2, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower709 : ∀ h, Pure node709 h → 11 ≤ h.length := by
  apply indexed_extend node709 [(0, node85), (5, node197)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower85
  · exact lower197
def node710 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]]
theorem lower710 : ∀ h, Pure node710 h → 11 ≤ h.length := by
  apply indexed_extend node710 [(0, node87), (2, node50), (10, node210)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower87
  · exact lower50
  · exact lower210
def node711 : Graph := [[0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower711 : ∀ h, Pure node711 h → 11 ≤ h.length := by
  apply indexed_extend node711 [(0, node59), (5, node198)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower59
  · exact lower198
def entries177 : List Graph := [node708, node709, node710, node711]
theorem entries_count177 : entries177.length = 4 := by decide +kernel
theorem census_node708 : ((verts node708).filter (wye node708)).length = 3 := by decide +kernel
theorem census_node709 : ((verts node709).filter (wye node709)).length = 2 := by decide +kernel
theorem census_node710 : ((verts node710).filter (wye node710)).length = 3 := by decide +kernel
theorem census_node711 : ((verts node711).filter (wye node711)).length = 2 := by decide +kernel
theorem arc_count177 : (entries177.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries177, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node708, census_node709, census_node710, census_node711]
  decide +kernel
end RawCert
