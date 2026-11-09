import Closure138
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node556 : Graph := [[0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0]]
theorem lower556 : ∀ h, Pure node556 h → 11 ≤ h.length := by
  apply indexed_extend node556 [(0, node272), (7, node116), (11, node141)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower272
  · exact lower116
  · exact lower141
def node557 : Graph := [[0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower557 : ∀ h, Pure node557 h → 11 ≤ h.length := by
  apply indexed_extend node557 [(0, node254), (1, node206), (12, node116)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower254
  · exact lower206
  · exact lower116
def node558 : Graph := [[0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower558 : ∀ h, Pure node558 h → 11 ≤ h.length := by
  apply indexed_extend node558 [(0, node273), (12, node116)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower273
  · exact lower116
def node559 : Graph := [[0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0], [0, 0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0]]
theorem lower559 : ∀ h, Pure node559 h → 11 ≤ h.length := by
  apply indexed_extend node559 [(0, node274), (3, node98), (10, node142)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower274
  · exact lower98
  · exact lower142
def entries139 : List Graph := [node556, node557, node558, node559]
theorem entries_count139 : entries139.length = 4 := by decide +kernel
theorem census_node556 : ((verts node556).filter (wye node556)).length = 3 := by decide +kernel
theorem census_node557 : ((verts node557).filter (wye node557)).length = 3 := by decide +kernel
theorem census_node558 : ((verts node558).filter (wye node558)).length = 2 := by decide +kernel
theorem census_node559 : ((verts node559).filter (wye node559)).length = 3 := by decide +kernel
theorem arc_count139 : (entries139.map (fun g => ((verts g).filter (wye g)).length)).sum = 11 := by
  simp only [entries139, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node556, census_node557, census_node558, census_node559]
  decide +kernel
end RawCert
