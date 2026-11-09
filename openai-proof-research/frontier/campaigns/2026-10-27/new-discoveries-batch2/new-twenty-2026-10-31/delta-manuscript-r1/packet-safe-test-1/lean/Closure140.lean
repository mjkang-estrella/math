import Closure139
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node560 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0], [0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0]]
theorem lower560 : ∀ h, Pure node560 h → 11 ≤ h.length := by
  apply indexed_extend node560 [(5, node119)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower119
def node561 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 1], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0]]
theorem lower561 : ∀ h, Pure node561 h → 11 ≤ h.length := by
  apply indexed_extend node561 [(1, node210), (2, node207), (8, node117)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower210
  · exact lower207
  · exact lower117
def node562 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 2, 1, 0]]
theorem lower562 : ∀ h, Pure node562 h → 11 ≤ h.length := by
  apply indexed_extend node562 [(1, node211), (2, node208)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower211
  · exact lower208
def node563 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1], [2, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 1, 1, 0]]
theorem lower563 : ∀ h, Pure node563 h → 11 ≤ h.length := by
  apply indexed_extend node563 [(2, node209), (8, node117)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower209
  · exact lower117
def entries140 : List Graph := [node560, node561, node562, node563]
theorem entries_count140 : entries140.length = 4 := by decide +kernel
theorem census_node560 : ((verts node560).filter (wye node560)).length = 1 := by decide +kernel
theorem census_node561 : ((verts node561).filter (wye node561)).length = 3 := by decide +kernel
theorem census_node562 : ((verts node562).filter (wye node562)).length = 2 := by decide +kernel
theorem census_node563 : ((verts node563).filter (wye node563)).length = 2 := by decide +kernel
theorem arc_count140 : (entries140.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by
  simp only [entries140, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node560, census_node561, census_node562, census_node563]
  decide +kernel
end RawCert
