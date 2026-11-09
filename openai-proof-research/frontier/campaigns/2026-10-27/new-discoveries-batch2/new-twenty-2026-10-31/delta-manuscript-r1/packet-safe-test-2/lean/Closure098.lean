import Closure097
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node392 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]]
theorem lower392 : ∀ h, Pure node392 h → 11 ≤ h.length := by
  apply indexed_extend node392 [(6, node76), (8, node60)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower76
  · exact lower60
def node393 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [0, 1, 2, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0], [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0]]
theorem lower393 : ∀ h, Pure node393 h → 11 ≤ h.length := by
  apply indexed_extend node393 [(6, node82), (9, node60)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower82
  · exact lower60
def node394 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower394 : ∀ h, Pure node394 h → 11 ≤ h.length := by
  apply indexed_extend node394 [(2, node145), (6, node83), (8, node61), (10, node60)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower145
  · exact lower83
  · exact lower61
  · exact lower60
def node395 : Graph := [[0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower395 : ∀ h, Pure node395 h → 11 ≤ h.length := by
  apply indexed_extend node395 [(8, node61)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower61
def entries98 : List Graph := [node392, node393, node394, node395]
theorem entries_count98 : entries98.length = 4 := by decide +kernel
theorem census_node392 : ((verts node392).filter (wye node392)).length = 2 := by decide +kernel
theorem census_node393 : ((verts node393).filter (wye node393)).length = 2 := by decide +kernel
theorem census_node394 : ((verts node394).filter (wye node394)).length = 4 := by decide +kernel
theorem census_node395 : ((verts node395).filter (wye node395)).length = 1 := by decide +kernel
theorem arc_count98 : (entries98.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries98, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node392, census_node393, census_node394, census_node395]
  decide +kernel
end RawCert
