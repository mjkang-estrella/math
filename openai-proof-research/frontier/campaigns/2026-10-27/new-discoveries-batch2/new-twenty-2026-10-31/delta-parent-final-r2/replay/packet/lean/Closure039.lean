import Closure038
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node156 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 3, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 1], [0, 1, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 1], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower156 : ∀ h, Pure node156 h → 11 ≤ h.length := by
  apply indexed_extend node156 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node157 : Graph := [[0, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [1, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1, 0], [1, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower157 : ∀ h, Pure node157 h → 11 ≤ h.length := by
  apply indexed_extend node157 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node158 : Graph := [[0, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [1, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 1], [1, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 1, 1, 0, 1, 2, 0, 0, 0]]
theorem lower158 : ∀ h, Pure node158 h → 11 ≤ h.length := by
  apply indexed_extend node158 [(8, node9)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower9
def node159 : Graph := [[0, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [1, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2], [1, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0]]
theorem lower159 : ∀ h, Pure node159 h → 11 ≤ h.length := by
  apply indexed_extend node159 [(8, node10)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower10
def entries39 : List Graph := [node156, node157, node158, node159]
theorem entries_count39 : entries39.length = 4 := by decide +kernel
theorem census_node156 : ((verts node156).filter (wye node156)).length = 0 := by decide +kernel
theorem census_node157 : ((verts node157).filter (wye node157)).length = 0 := by decide +kernel
theorem census_node158 : ((verts node158).filter (wye node158)).length = 1 := by decide +kernel
theorem census_node159 : ((verts node159).filter (wye node159)).length = 1 := by decide +kernel
theorem arc_count39 : (entries39.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by
  simp only [entries39, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node156, census_node157, census_node158, census_node159]
  decide +kernel
end RawCert
