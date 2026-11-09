import Closure040
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node164 : Graph := [[0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [1, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [1, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower164 : ∀ h, Pure node164 h → 11 ≤ h.length := by
  apply indexed_extend node164 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node165 : Graph := [[0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [1, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [1, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 1, 0, 1, 0, 1, 2, 0, 0, 0]]
theorem lower165 : ∀ h, Pure node165 h → 11 ≤ h.length := by
  apply indexed_extend node165 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node166 : Graph := [[0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0, 0], [1, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0], [1, 0, 1, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower166 : ∀ h, Pure node166 h → 11 ≤ h.length := by
  apply indexed_extend node166 [(11, node11)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower11
def node167 : Graph := [[0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [1, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower167 : ∀ h, Pure node167 h → 11 ≤ h.length := by
  apply indexed_extend node167 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries41 : List Graph := [node164, node165, node166, node167]
theorem entries_count41 : entries41.length = 4 := by decide +kernel
theorem census_node164 : ((verts node164).filter (wye node164)).length = 0 := by decide +kernel
theorem census_node165 : ((verts node165).filter (wye node165)).length = 0 := by decide +kernel
theorem census_node166 : ((verts node166).filter (wye node166)).length = 1 := by decide +kernel
theorem census_node167 : ((verts node167).filter (wye node167)).length = 0 := by decide +kernel
theorem arc_count41 : (entries41.map (fun g => ((verts g).filter (wye g)).length)).sum = 1 := by
  simp only [entries41, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node164, census_node165, census_node166, census_node167]
  decide +kernel
end RawCert
