import Closure086
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node348 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1, 1, 2, 0, 0, 0]]
theorem lower348 : ∀ h, Pure node348 h → 11 ≤ h.length := by
  apply indexed_extend node348 [(1, node95), (11, node42)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower95
  · exact lower42
def node349 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower349 : ∀ h, Pure node349 h → 11 ≤ h.length := by
  apply indexed_extend node349 [(2, node96), (12, node43)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower96
  · exact lower43
def node350 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2], [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower350 : ∀ h, Pure node350 h → 11 ≤ h.length := by
  apply indexed_extend node350 [(2, node97), (12, node44)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower97
  · exact lower44
def node351 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower351 : ∀ h, Pure node351 h → 11 ≤ h.length := by
  apply indexed_extend node351 [(4, node73), (12, node40)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower73
  · exact lower40
def entries87 : List Graph := [node348, node349, node350, node351]
theorem entries_count87 : entries87.length = 4 := by decide +kernel
theorem census_node348 : ((verts node348).filter (wye node348)).length = 2 := by decide +kernel
theorem census_node349 : ((verts node349).filter (wye node349)).length = 2 := by decide +kernel
theorem census_node350 : ((verts node350).filter (wye node350)).length = 2 := by decide +kernel
theorem census_node351 : ((verts node351).filter (wye node351)).length = 2 := by decide +kernel
theorem arc_count87 : (entries87.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by
  simp only [entries87, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node348, census_node349, census_node350, census_node351]
  decide +kernel
end RawCert
