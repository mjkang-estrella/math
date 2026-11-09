import Closure050
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node204 : Graph := [[0, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 2, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0], [1, 0, 1, 1, 2, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower204 : ∀ h, Pure node204 h → 11 ≤ h.length := by
  apply indexed_extend node204 [(11, node15)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower15
def node205 : Graph := [[0, 0, 2, 1, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 2], [1, 0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 2, 0, 0], [2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1, 0]]
theorem lower205 : ∀ h, Pure node205 h → 11 ≤ h.length := by
  apply indexed_extend node205 [(9, node16)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower16
def node206 : Graph := [[0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [2, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower206 : ∀ h, Pure node206 h → 11 ≤ h.length := by
  apply indexed_extend node206 [(0, node1)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower1
def node207 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 1], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0]]
theorem lower207 : ∀ h, Pure node207 h → 11 ≤ h.length := by
  apply indexed_extend node207 [(7, node17)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower17
def entries51 : List Graph := [node204, node205, node206, node207]
theorem entries_count51 : entries51.length = 4 := by decide +kernel
theorem census_node204 : ((verts node204).filter (wye node204)).length = 1 := by decide +kernel
theorem census_node205 : ((verts node205).filter (wye node205)).length = 1 := by decide +kernel
theorem census_node206 : ((verts node206).filter (wye node206)).length = 1 := by decide +kernel
theorem census_node207 : ((verts node207).filter (wye node207)).length = 1 := by decide +kernel
theorem arc_count51 : (entries51.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by
  simp only [entries51, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node204, census_node205, census_node206, census_node207]
  decide +kernel
end RawCert
