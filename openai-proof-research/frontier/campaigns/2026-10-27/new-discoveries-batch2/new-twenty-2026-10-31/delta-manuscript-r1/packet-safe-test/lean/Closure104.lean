import Closure103
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node416 : Graph := [[0, 0, 0, 1, 0, 1, 0, 1, 0, 3, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 1], [1, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 2, 1, 0]]
theorem lower416 : ∀ h, Pure node416 h → 11 ≤ h.length := by
  apply indexed_extend node416 [(2, node160), (10, node66)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower160
  · exact lower66
def node417 : Graph := [[0, 0, 0, 1, 0, 1, 0, 1, 0, 3, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [1, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 2], [1, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower417 : ∀ h, Pure node417 h → 11 ≤ h.length := by
  apply indexed_extend node417 [(2, node161), (10, node67)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower161
  · exact lower67
def node418 : Graph := [[0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0]]
theorem lower418 : ∀ h, Pure node418 h → 11 ≤ h.length := by
  apply indexed_extend node418 [(7, node69), (9, node68)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower69
  · exact lower68
def node419 : Graph := [[0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower419 : ∀ h, Pure node419 h → 11 ≤ h.length := by
  apply indexed_extend node419 [(5, node71), (7, node70)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower71
  · exact lower70
def entries104 : List Graph := [node416, node417, node418, node419]
theorem entries_count104 : entries104.length = 4 := by decide +kernel
theorem census_node416 : ((verts node416).filter (wye node416)).length = 2 := by decide +kernel
theorem census_node417 : ((verts node417).filter (wye node417)).length = 2 := by decide +kernel
theorem census_node418 : ((verts node418).filter (wye node418)).length = 2 := by decide +kernel
theorem census_node419 : ((verts node419).filter (wye node419)).length = 2 := by decide +kernel
theorem arc_count104 : (entries104.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by
  simp only [entries104, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node416, census_node417, census_node418, census_node419]
  decide +kernel
end RawCert
