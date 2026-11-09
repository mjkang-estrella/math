import Closure264
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1060 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1060 : ∀ h, Pure node1060 h → 11 ≤ h.length := by
  apply indexed_extend node1060 [(2, node514), (4, node676), (7, node369), (9, node364), (11, node337)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower514
  · exact lower676
  · exact lower369
  · exact lower364
  · exact lower337
def node1061 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 2], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1061 : ∀ h, Pure node1061 h → 11 ≤ h.length := by
  apply indexed_extend node1061 [(2, node515), (4, node677), (9, node365), (11, node338), (13, node335)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower515
  · exact lower677
  · exact lower365
  · exact lower338
  · exact lower335
def node1062 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1062 : ∀ h, Pure node1062 h → 11 ≤ h.length := by
  apply indexed_extend node1062 [(2, node516), (6, node369), (9, node366), (11, node339), (13, node336)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower516
  · exact lower369
  · exact lower366
  · exact lower339
  · exact lower336
def node1063 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1063 : ∀ h, Pure node1063 h → 11 ≤ h.length := by
  apply indexed_extend node1063 [(2, node517), (4, node672), (9, node367), (11, node342)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower517
  · exact lower672
  · exact lower367
  · exact lower342
def entries265 : List Graph := [node1060, node1061, node1062, node1063]
theorem entries_count265 : entries265.length = 4 := by decide +kernel
theorem census_node1060 : ((verts node1060).filter (wye node1060)).length = 5 := by decide +kernel
theorem census_node1061 : ((verts node1061).filter (wye node1061)).length = 5 := by decide +kernel
theorem census_node1062 : ((verts node1062).filter (wye node1062)).length = 5 := by decide +kernel
theorem census_node1063 : ((verts node1063).filter (wye node1063)).length = 4 := by decide +kernel
theorem arc_count265 : (entries265.map (fun g => ((verts g).filter (wye g)).length)).sum = 19 := by
  simp only [entries265, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1060, census_node1061, census_node1062, census_node1063]
  decide +kernel
end RawCert
