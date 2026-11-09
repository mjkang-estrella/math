import Closure153
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node616 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0]]
theorem lower616 : ∀ h, Pure node616 h → 11 ≤ h.length := by
  apply indexed_extend node616 [(5, node133), (7, node138)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower133
  · exact lower138
def node617 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0]]
theorem lower617 : ∀ h, Pure node617 h → 11 ≤ h.length := by
  apply indexed_extend node617 [(5, node134), (7, node139)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower134
  · exact lower139
def node618 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0]]
theorem lower618 : ∀ h, Pure node618 h → 11 ≤ h.length := by
  apply indexed_extend node618 [(5, node135), (6, node136), (12, node127)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower135
  · exact lower136
  · exact lower127
def node619 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0]]
theorem lower619 : ∀ h, Pure node619 h → 11 ≤ h.length := by
  apply indexed_extend node619 [(5, node135), (12, node128)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower135
  · exact lower128
def entries154 : List Graph := [node616, node617, node618, node619]
theorem entries_count154 : entries154.length = 4 := by decide +kernel
theorem census_node616 : ((verts node616).filter (wye node616)).length = 2 := by decide +kernel
theorem census_node617 : ((verts node617).filter (wye node617)).length = 2 := by decide +kernel
theorem census_node618 : ((verts node618).filter (wye node618)).length = 3 := by decide +kernel
theorem census_node619 : ((verts node619).filter (wye node619)).length = 2 := by decide +kernel
theorem arc_count154 : (entries154.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries154, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node616, census_node617, census_node618, census_node619]
  decide +kernel
end RawCert
