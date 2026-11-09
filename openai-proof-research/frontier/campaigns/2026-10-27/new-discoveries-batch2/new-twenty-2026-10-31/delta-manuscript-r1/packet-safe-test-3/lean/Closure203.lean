import Closure202
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node812 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 0, 0, 1, 1, 0]]
theorem lower812 : ∀ h, Pure node812 h → 11 ≤ h.length := by
  apply indexed_extend node812 [(5, node236)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower236
def node813 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower813 : ∀ h, Pure node813 h → 11 ≤ h.length := by
  apply indexed_extend node813 [(5, node237)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower237
def node814 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0]]
theorem lower814 : ∀ h, Pure node814 h → 11 ≤ h.length := by
  apply indexed_extend node814 [(5, node238), (9, node210)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower238
  · exact lower210
def node815 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0], [1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0]]
theorem lower815 : ∀ h, Pure node815 h → 11 ≤ h.length := by
  apply indexed_extend node815 [(3, node223), (9, node211), (10, node210)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower223
  · exact lower211
  · exact lower210
def entries203 : List Graph := [node812, node813, node814, node815]
theorem entries_count203 : entries203.length = 4 := by decide +kernel
theorem census_node812 : ((verts node812).filter (wye node812)).length = 1 := by decide +kernel
theorem census_node813 : ((verts node813).filter (wye node813)).length = 1 := by decide +kernel
theorem census_node814 : ((verts node814).filter (wye node814)).length = 2 := by decide +kernel
theorem census_node815 : ((verts node815).filter (wye node815)).length = 3 := by decide +kernel
theorem arc_count203 : (entries203.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by
  simp only [entries203, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node812, census_node813, census_node814, census_node815]
  decide +kernel
end RawCert
