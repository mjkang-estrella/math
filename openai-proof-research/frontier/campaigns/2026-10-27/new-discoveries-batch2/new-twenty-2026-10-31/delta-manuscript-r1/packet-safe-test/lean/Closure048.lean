import Closure047
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node192 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 1], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [1, 0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 2, 0, 0, 1, 0, 1, 0]]
theorem lower192 : ∀ h, Pure node192 h → 11 ≤ h.length := by
  apply indexed_extend node192 [(6, node16)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower16
def node193 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0], [1, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 2, 0, 0, 1, 0, 1, 0]]
theorem lower193 : ∀ h, Pure node193 h → 11 ≤ h.length := by
  apply indexed_extend node193 [(6, node16), (9, node20)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower16
  · exact lower20
def node194 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 1], [1, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0]]
theorem lower194 : ∀ h, Pure node194 h → 11 ≤ h.length := by
  apply indexed_extend node194 [(2, node9), (9, node21)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower9
  · exact lower21
def node195 : Graph := [[0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 2], [1, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0]]
theorem lower195 : ∀ h, Pure node195 h → 11 ≤ h.length := by
  apply indexed_extend node195 [(2, node10), (5, node16)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower10
  · exact lower16
def entries48 : List Graph := [node192, node193, node194, node195]
theorem entries_count48 : entries48.length = 4 := by decide +kernel
theorem census_node192 : ((verts node192).filter (wye node192)).length = 1 := by decide +kernel
theorem census_node193 : ((verts node193).filter (wye node193)).length = 2 := by decide +kernel
theorem census_node194 : ((verts node194).filter (wye node194)).length = 2 := by decide +kernel
theorem census_node195 : ((verts node195).filter (wye node195)).length = 2 := by decide +kernel
theorem arc_count48 : (entries48.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by
  simp only [entries48, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node192, census_node193, census_node194, census_node195]
  decide +kernel
end RawCert
