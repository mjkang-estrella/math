import Closure180
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node724 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower724 : ∀ h, Pure node724 h → 11 ≤ h.length := by
  apply indexed_extend node724 [(0, node168), (6, node183), (10, node224)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower168
  · exact lower183
  · exact lower224
def node725 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower725 : ∀ h, Pure node725 h → 11 ≤ h.length := by
  apply indexed_extend node725 [(0, node169), (2, node96), (5, node183)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower169
  · exact lower96
  · exact lower183
def node726 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0], [0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower726 : ∀ h, Pure node726 h → 11 ≤ h.length := by
  apply indexed_extend node726 [(0, node170), (2, node97), (10, node221)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower170
  · exact lower97
  · exact lower221
def node727 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3], [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower727 : ∀ h, Pure node727 h → 11 ≤ h.length := by
  apply indexed_extend node727 [(0, node177), (3, node206)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower177
  · exact lower206
def entries181 : List Graph := [node724, node725, node726, node727]
theorem entries_count181 : entries181.length = 4 := by decide +kernel
theorem census_node724 : ((verts node724).filter (wye node724)).length = 3 := by decide +kernel
theorem census_node725 : ((verts node725).filter (wye node725)).length = 3 := by decide +kernel
theorem census_node726 : ((verts node726).filter (wye node726)).length = 3 := by decide +kernel
theorem census_node727 : ((verts node727).filter (wye node727)).length = 2 := by decide +kernel
theorem arc_count181 : (entries181.map (fun g => ((verts g).filter (wye g)).length)).sum = 11 := by
  simp only [entries181, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node724, census_node725, census_node726, census_node727]
  decide +kernel
end RawCert
