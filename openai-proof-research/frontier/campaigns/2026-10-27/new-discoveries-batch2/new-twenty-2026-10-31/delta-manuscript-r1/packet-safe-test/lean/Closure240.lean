import Closure239
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node960 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 1, 0], [0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2], [1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 0]]
theorem lower960 : ∀ h, Pure node960 h → 11 ≤ h.length := by
  apply indexed_extend node960 [(3, node280)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower280
def node961 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 2, 0, 0]]
theorem lower961 : ∀ h, Pure node961 h → 11 ≤ h.length := by
  apply indexed_extend node961 [(8, node277)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower277
def node962 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 2], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 2, 0, 0]]
theorem lower962 : ∀ h, Pure node962 h → 11 ≤ h.length := by
  apply indexed_extend node962 [(6, node276)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower276
def node963 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 1, 0], [0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 2, 0, 0]]
theorem lower963 : ∀ h, Pure node963 h → 11 ≤ h.length := by
  apply indexed_extend node963 [(7, node277)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower277
def entries240 : List Graph := [node960, node961, node962, node963]
theorem entries_count240 : entries240.length = 4 := by decide +kernel
theorem census_node960 : ((verts node960).filter (wye node960)).length = 1 := by decide +kernel
theorem census_node961 : ((verts node961).filter (wye node961)).length = 1 := by decide +kernel
theorem census_node962 : ((verts node962).filter (wye node962)).length = 1 := by decide +kernel
theorem census_node963 : ((verts node963).filter (wye node963)).length = 1 := by decide +kernel
theorem arc_count240 : (entries240.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by
  simp only [entries240, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node960, census_node961, census_node962, census_node963]
  decide +kernel
end RawCert
