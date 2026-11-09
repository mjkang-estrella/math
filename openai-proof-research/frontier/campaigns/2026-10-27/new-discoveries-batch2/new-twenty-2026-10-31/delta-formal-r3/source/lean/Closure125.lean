import Closure124
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node500 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0], [1, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower500 : ∀ h, Pure node500 h → 11 ≤ h.length := by
  apply indexed_extend node500 [(5, node98), (12, node92)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower98
  · exact lower92
def node501 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0]]
theorem lower501 : ∀ h, Pure node501 h → 11 ≤ h.length := by
  apply indexed_extend node501 [(7, node98)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower98
def node502 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0], [0, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0]]
theorem lower502 : ∀ h, Pure node502 h → 11 ≤ h.length := by
  apply indexed_extend node502 [(3, node62), (5, node99), (6, node100)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower62
  · exact lower99
  · exact lower100
def node503 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 2, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [1, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0]]
theorem lower503 : ∀ h, Pure node503 h → 11 ≤ h.length := by
  apply indexed_extend node503 [(3, node68), (5, node101), (8, node99), (11, node127)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower68
  · exact lower101
  · exact lower99
  · exact lower127
def entries125 : List Graph := [node500, node501, node502, node503]
theorem entries_count125 : entries125.length = 4 := by decide +kernel
theorem census_node500 : ((verts node500).filter (wye node500)).length = 2 := by decide +kernel
theorem census_node501 : ((verts node501).filter (wye node501)).length = 1 := by decide +kernel
theorem census_node502 : ((verts node502).filter (wye node502)).length = 3 := by decide +kernel
theorem census_node503 : ((verts node503).filter (wye node503)).length = 4 := by decide +kernel
theorem arc_count125 : (entries125.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by
  simp only [entries125, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node500, census_node501, census_node502, census_node503]
  decide +kernel
end RawCert
