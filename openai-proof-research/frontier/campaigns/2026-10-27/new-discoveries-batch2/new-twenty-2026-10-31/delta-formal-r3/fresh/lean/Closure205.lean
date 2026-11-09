import Closure204
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node820 : Graph := [[0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower820 : ∀ h, Pure node820 h → 11 ≤ h.length := by
  apply indexed_extend node820 [(3, node225), (5, node246), (10, node212)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower225
  · exact lower246
  · exact lower212
def node821 : Graph := [[0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower821 : ∀ h, Pure node821 h → 11 ≤ h.length := by
  apply indexed_extend node821 [(5, node247), (10, node212)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower247
  · exact lower212
def node822 : Graph := [[0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [1, 0, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower822 : ∀ h, Pure node822 h → 11 ≤ h.length := by
  apply indexed_extend node822 [(3, node226), (5, node248), (8, node214), (10, node213)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower226
  · exact lower248
  · exact lower214
  · exact lower213
def node823 : Graph := [[0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [1, 0, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 2, 0, 0]]
theorem lower823 : ∀ h, Pure node823 h → 11 ≤ h.length := by
  apply indexed_extend node823 [(5, node249), (8, node215), (10, node213)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower249
  · exact lower215
  · exact lower213
def entries205 : List Graph := [node820, node821, node822, node823]
theorem entries_count205 : entries205.length = 4 := by decide +kernel
theorem census_node820 : ((verts node820).filter (wye node820)).length = 3 := by decide +kernel
theorem census_node821 : ((verts node821).filter (wye node821)).length = 2 := by decide +kernel
theorem census_node822 : ((verts node822).filter (wye node822)).length = 4 := by decide +kernel
theorem census_node823 : ((verts node823).filter (wye node823)).length = 3 := by decide +kernel
theorem arc_count205 : (entries205.map (fun g => ((verts g).filter (wye g)).length)).sum = 12 := by
  simp only [entries205, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node820, census_node821, census_node822, census_node823]
  decide +kernel
end RawCert
