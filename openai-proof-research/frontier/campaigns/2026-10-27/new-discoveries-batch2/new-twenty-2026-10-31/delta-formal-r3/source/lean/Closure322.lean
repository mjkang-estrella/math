import Closure321
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1288 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 1], [1, 0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 2, 0, 0, 0]]
theorem lower1288 : ∀ h, Pure node1288 h → 11 ≤ h.length := by
  apply indexed_extend node1288 [(2, node772), (3, node412), (10, node539), (11, node632), (12, node532)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower772
  · exact lower412
  · exact lower539
  · exact lower632
  · exact lower532
def node1289 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0]]
theorem lower1289 : ∀ h, Pure node1289 h → 11 ≤ h.length := by
  apply indexed_extend node1289 [(2, node773), (3, node413), (6, node549), (10, node540), (12, node533)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower773
  · exact lower413
  · exact lower549
  · exact lower540
  · exact lower533
def node1290 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [1, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1290 : ∀ h, Pure node1290 h → 11 ≤ h.length := by
  apply indexed_extend node1290 [(3, node425), (5, node550), (9, node541), (12, node523), (13, node522)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower425
  · exact lower550
  · exact lower541
  · exact lower523
  · exact lower522
def node1291 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower1291 : ∀ h, Pure node1291 h → 11 ≤ h.length := by
  apply indexed_extend node1291 [(5, node550), (7, node551), (9, node542), (12, node525), (13, node524)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower550
  · exact lower551
  · exact lower542
  · exact lower525
  · exact lower524
def entries322 : List Graph := [node1288, node1289, node1290, node1291]
theorem entries_count322 : entries322.length = 4 := by decide +kernel
theorem census_node1288 : ((verts node1288).filter (wye node1288)).length = 5 := by decide +kernel
theorem census_node1289 : ((verts node1289).filter (wye node1289)).length = 5 := by decide +kernel
theorem census_node1290 : ((verts node1290).filter (wye node1290)).length = 5 := by decide +kernel
theorem census_node1291 : ((verts node1291).filter (wye node1291)).length = 5 := by decide +kernel
theorem arc_count322 : (entries322.map (fun g => ((verts g).filter (wye g)).length)).sum = 20 := by
  simp only [entries322, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1288, census_node1289, census_node1290, census_node1291]
  decide +kernel
end RawCert
