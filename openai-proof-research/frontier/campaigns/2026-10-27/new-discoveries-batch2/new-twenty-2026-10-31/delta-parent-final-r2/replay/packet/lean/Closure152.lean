import Closure151
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node608 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 1, 1, 0]]
theorem lower608 : ∀ h, Pure node608 h → 11 ≤ h.length := by
  apply indexed_extend node608 [(1, node236), (2, node230), (7, node130)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower236
  · exact lower230
  · exact lower130
def node609 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1, 0]]
theorem lower609 : ∀ h, Pure node609 h → 11 ≤ h.length := by
  apply indexed_extend node609 [(1, node237), (2, node231)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower237
  · exact lower231
def node610 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0]]
theorem lower610 : ∀ h, Pure node610 h → 11 ≤ h.length := by
  apply indexed_extend node610 [(1, node238), (2, node232), (7, node131)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower238
  · exact lower232
  · exact lower131
def node611 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 2, 1, 0]]
theorem lower611 : ∀ h, Pure node611 h → 11 ≤ h.length := by
  apply indexed_extend node611 [(1, node239), (2, node233)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower239
  · exact lower233
def entries152 : List Graph := [node608, node609, node610, node611]
theorem entries_count152 : entries152.length = 4 := by decide +kernel
theorem census_node608 : ((verts node608).filter (wye node608)).length = 3 := by decide +kernel
theorem census_node609 : ((verts node609).filter (wye node609)).length = 2 := by decide +kernel
theorem census_node610 : ((verts node610).filter (wye node610)).length = 3 := by decide +kernel
theorem census_node611 : ((verts node611).filter (wye node611)).length = 2 := by decide +kernel
theorem arc_count152 : (entries152.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries152, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node608, census_node609, census_node610, census_node611]
  decide +kernel
end RawCert
