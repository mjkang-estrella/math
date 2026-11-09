import Closure307
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1232 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1232 : ∀ h, Pure node1232 h → 11 ≤ h.length := by
  apply indexed_extend node1232 [(2, node740), (3, node678), (7, node486), (8, node487), (9, node488)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower740
  · exact lower678
  · exact lower486
  · exact lower487
  · exact lower488
def node1233 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0]]
theorem lower1233 : ∀ h, Pure node1233 h → 11 ≤ h.length := by
  apply indexed_extend node1233 [(3, node679), (5, node491), (7, node489), (8, node490)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower679
  · exact lower491
  · exact lower489
  · exact lower490
def node1234 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1234 : ∀ h, Pure node1234 h → 11 ≤ h.length := by
  apply indexed_extend node1234 [(6, node494), (7, node492), (8, node493)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower494
  · exact lower492
  · exact lower493
def node1235 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 3], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower1235 : ∀ h, Pure node1235 h → 11 ≤ h.length := by
  apply indexed_extend node1235 [(2, node740), (7, node495), (8, node496)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower740
  · exact lower495
  · exact lower496
def entries308 : List Graph := [node1232, node1233, node1234, node1235]
theorem entries_count308 : entries308.length = 4 := by decide +kernel
theorem census_node1232 : ((verts node1232).filter (wye node1232)).length = 5 := by decide +kernel
theorem census_node1233 : ((verts node1233).filter (wye node1233)).length = 4 := by decide +kernel
theorem census_node1234 : ((verts node1234).filter (wye node1234)).length = 3 := by decide +kernel
theorem census_node1235 : ((verts node1235).filter (wye node1235)).length = 3 := by decide +kernel
theorem arc_count308 : (entries308.map (fun g => ((verts g).filter (wye g)).length)).sum = 15 := by
  simp only [entries308, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1232, census_node1233, census_node1234, census_node1235]
  decide +kernel
end RawCert
