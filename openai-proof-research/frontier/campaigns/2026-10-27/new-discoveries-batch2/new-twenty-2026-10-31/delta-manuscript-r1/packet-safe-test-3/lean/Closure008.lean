import Closure007
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node32 : Graph := [[0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 2, 0, 1, 0, 1, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 1, 0, 1, 1, 2, 0, 0, 0]]
theorem lower32 : ∀ h, Pure node32 h → 11 ≤ h.length := by
  apply indexed_extend node32 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node33 : Graph := [[0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [0, 1, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower33 : ∀ h, Pure node33 h → 11 ≤ h.length := by
  apply indexed_extend node33 [(11, node0)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower0
def node34 : Graph := [[0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [0, 1, 2, 0, 1, 0, 1, 0, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 2, 0, 2, 0, 0]]
theorem lower34 : ∀ h, Pure node34 h → 11 ≤ h.length := by
  apply indexed_extend node34 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node35 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, 0], [0, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1, 1, 1, 2, 0, 0]]
theorem lower35 : ∀ h, Pure node35 h → 11 ≤ h.length := by
  apply indexed_extend node35 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries8 : List Graph := [node32, node33, node34, node35]
theorem entries_count8 : entries8.length = 4 := by decide +kernel
theorem census_node32 : ((verts node32).filter (wye node32)).length = 0 := by decide +kernel
theorem census_node33 : ((verts node33).filter (wye node33)).length = 1 := by decide +kernel
theorem census_node34 : ((verts node34).filter (wye node34)).length = 0 := by decide +kernel
theorem census_node35 : ((verts node35).filter (wye node35)).length = 0 := by decide +kernel
theorem arc_count8 : (entries8.map (fun g => ((verts g).filter (wye g)).length)).sum = 1 := by
  simp only [entries8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node32, census_node33, census_node34, census_node35]
  decide +kernel
end RawCert
