import Closure022
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node92 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0]]
theorem lower92 : ∀ h, Pure node92 h → 11 ≤ h.length := by
  apply indexed_extend node92 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node93 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower93 : ∀ h, Pure node93 h → 11 ≤ h.length := by
  apply indexed_extend node93 [(3, node11)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower11
def node94 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 0], [0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0]]
theorem lower94 : ∀ h, Pure node94 h → 11 ≤ h.length := by
  apply indexed_extend node94 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node95 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 1, 0, 1, 1, 2, 0, 0, 0]]
theorem lower95 : ∀ h, Pure node95 h → 11 ≤ h.length := by
  apply indexed_extend node95 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries23 : List Graph := [node92, node93, node94, node95]
theorem entries_count23 : entries23.length = 4 := by decide +kernel
theorem census_node92 : ((verts node92).filter (wye node92)).length = 0 := by decide +kernel
theorem census_node93 : ((verts node93).filter (wye node93)).length = 1 := by decide +kernel
theorem census_node94 : ((verts node94).filter (wye node94)).length = 0 := by decide +kernel
theorem census_node95 : ((verts node95).filter (wye node95)).length = 0 := by decide +kernel
theorem arc_count23 : (entries23.map (fun g => ((verts g).filter (wye g)).length)).sum = 1 := by
  simp only [entries23, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node92, census_node93, census_node94, census_node95]
  decide +kernel
end RawCert
