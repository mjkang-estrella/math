import Closure003
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node16 : Graph := [[0, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 2], [1, 0, 1, 1, 0, 2, 0, 0, 1, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 2, 0, 1, 0, 1, 0]]
theorem lower16 : ∀ h, Pure node16 h → 11 ≤ h.length := by
  apply indexed_extend node16 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node17 : Graph := [[0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 3, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 1], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 1], [1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 1], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0]]
theorem lower17 : ∀ h, Pure node17 h → 11 ≤ h.length := by
  apply indexed_extend node17 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node18 : Graph := [[0, 0, 3, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 1], [1, 0, 1, 0, 1, 2, 0, 0, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 1, 0, 2, 1, 0]]
theorem lower18 : ∀ h, Pure node18 h → 11 ≤ h.length := by
  apply indexed_extend node18 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node19 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3], [3, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 0, 1, 0, 0, 0, 2, 1, 1, 1, 0], [0, 2, 0, 1, 0, 0, 0, 0, 1, 1, 1], [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 0, 0, 3, 1, 1, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0]]
theorem lower19 : ∀ h, Pure node19 h → 11 ≤ h.length := by
  apply indexed_extend node19 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries4 : List Graph := [node16, node17, node18, node19]
theorem entries_count4 : entries4.length = 4 := by decide +kernel
theorem census_node16 : ((verts node16).filter (wye node16)).length = 0 := by decide +kernel
theorem census_node17 : ((verts node17).filter (wye node17)).length = 0 := by decide +kernel
theorem census_node18 : ((verts node18).filter (wye node18)).length = 0 := by decide +kernel
theorem census_node19 : ((verts node19).filter (wye node19)).length = 0 := by decide +kernel
theorem arc_count4 : (entries4.map (fun g => ((verts g).filter (wye g)).length)).sum = 0 := by
  simp only [entries4, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node16, census_node17, census_node18, census_node19]
  decide +kernel
end RawCert
