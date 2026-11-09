import Closure102
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node412 : Graph := [[0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 1], [1, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 1, 1, 0, 1, 2, 0, 0, 0]]
theorem lower412 : ∀ h, Pure node412 h → 11 ≤ h.length := by
  apply indexed_extend node412 [(2, node158), (9, node66), (11, node64)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower158
  · exact lower66
  · exact lower64
def node413 : Graph := [[0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0]]
theorem lower413 : ∀ h, Pure node413 h → 11 ≤ h.length := by
  apply indexed_extend node413 [(2, node159), (9, node67), (11, node65)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower159
  · exact lower67
  · exact lower65
def node414 : Graph := [[0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 1], [1, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 2, 0]]
theorem lower414 : ∀ h, Pure node414 h → 11 ≤ h.length := by
  apply indexed_extend node414 [(11, node64)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower64
def node415 : Graph := [[0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower415 : ∀ h, Pure node415 h → 11 ≤ h.length := by
  apply indexed_extend node415 [(11, node65), (12, node63)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower65
  · exact lower63
def entries103 : List Graph := [node412, node413, node414, node415]
theorem entries_count103 : entries103.length = 4 := by decide +kernel
theorem census_node412 : ((verts node412).filter (wye node412)).length = 3 := by decide +kernel
theorem census_node413 : ((verts node413).filter (wye node413)).length = 3 := by decide +kernel
theorem census_node414 : ((verts node414).filter (wye node414)).length = 1 := by decide +kernel
theorem census_node415 : ((verts node415).filter (wye node415)).length = 2 := by decide +kernel
theorem arc_count103 : (entries103.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries103, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node412, census_node413, census_node414, census_node415]
  decide +kernel
end RawCert
