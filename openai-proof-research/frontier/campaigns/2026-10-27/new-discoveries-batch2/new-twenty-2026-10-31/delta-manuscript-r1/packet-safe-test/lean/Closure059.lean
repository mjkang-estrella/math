import Closure058
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node236 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 2, 0, 0, 0, 1, 1, 0]]
theorem lower236 : ∀ h, Pure node236 h → 11 ≤ h.length := by
  apply indexed_extend node236 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node237 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1, 0]]
theorem lower237 : ∀ h, Pure node237 h → 11 ≤ h.length := by
  apply indexed_extend node237 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node238 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0]]
theorem lower238 : ∀ h, Pure node238 h → 11 ≤ h.length := by
  apply indexed_extend node238 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node239 : Graph := [[0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1], [1, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 1, 0, 2, 1, 0]]
theorem lower239 : ∀ h, Pure node239 h → 11 ≤ h.length := by
  apply indexed_extend node239 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries59 : List Graph := [node236, node237, node238, node239]
theorem entries_count59 : entries59.length = 4 := by decide +kernel
theorem census_node236 : ((verts node236).filter (wye node236)).length = 0 := by decide +kernel
theorem census_node237 : ((verts node237).filter (wye node237)).length = 0 := by decide +kernel
theorem census_node238 : ((verts node238).filter (wye node238)).length = 0 := by decide +kernel
theorem census_node239 : ((verts node239).filter (wye node239)).length = 0 := by decide +kernel
theorem arc_count59 : (entries59.map (fun g => ((verts g).filter (wye g)).length)).sum = 0 := by
  simp only [entries59, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node236, census_node237, census_node238, census_node239]
  decide +kernel
end RawCert
