import Closure060
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node244 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0], [1, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 0, 0]]
theorem lower244 : ∀ h, Pure node244 h → 11 ≤ h.length := by
  apply indexed_extend node244 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node245 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [1, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0]]
theorem lower245 : ∀ h, Pure node245 h → 11 ≤ h.length := by
  apply indexed_extend node245 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node246 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [1, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1, 0]]
theorem lower246 : ∀ h, Pure node246 h → 11 ≤ h.length := by
  apply indexed_extend node246 [(9, node20)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower20
def node247 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [1, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower247 : ∀ h, Pure node247 h → 11 ≤ h.length := by
  apply indexed_extend node247 [(9, node20)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower20
def entries61 : List Graph := [node244, node245, node246, node247]
theorem entries_count61 : entries61.length = 4 := by decide +kernel
theorem census_node244 : ((verts node244).filter (wye node244)).length = 0 := by decide +kernel
theorem census_node245 : ((verts node245).filter (wye node245)).length = 0 := by decide +kernel
theorem census_node246 : ((verts node246).filter (wye node246)).length = 1 := by decide +kernel
theorem census_node247 : ((verts node247).filter (wye node247)).length = 1 := by decide +kernel
theorem arc_count61 : (entries61.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by
  simp only [entries61, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node244, census_node245, census_node246, census_node247]
  decide +kernel
end RawCert
