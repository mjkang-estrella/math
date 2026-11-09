import Closure164
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node660 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower660 : ∀ h, Pure node660 h → 11 ≤ h.length := by
  apply indexed_extend node660 [(6, node159), (9, node147)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower159
  · exact lower147
def node661 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 0, 0]]
theorem lower661 : ∀ h, Pure node661 h → 11 ≤ h.length := by
  apply indexed_extend node661 [(5, node158), (9, node148)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower158
  · exact lower148
def node662 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower662 : ∀ h, Pure node662 h → 11 ≤ h.length := by
  apply indexed_extend node662 [(6, node157)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower157
def node663 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower663 : ∀ h, Pure node663 h → 11 ≤ h.length := by
  apply indexed_extend node663 [(5, node158), (6, node159), (9, node149)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower158
  · exact lower159
  · exact lower149
def entries165 : List Graph := [node660, node661, node662, node663]
theorem entries_count165 : entries165.length = 4 := by decide +kernel
theorem census_node660 : ((verts node660).filter (wye node660)).length = 2 := by decide +kernel
theorem census_node661 : ((verts node661).filter (wye node661)).length = 2 := by decide +kernel
theorem census_node662 : ((verts node662).filter (wye node662)).length = 1 := by decide +kernel
theorem census_node663 : ((verts node663).filter (wye node663)).length = 3 := by decide +kernel
theorem arc_count165 : (entries165.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by
  simp only [entries165, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node660, census_node661, census_node662, census_node663]
  decide +kernel
end RawCert
