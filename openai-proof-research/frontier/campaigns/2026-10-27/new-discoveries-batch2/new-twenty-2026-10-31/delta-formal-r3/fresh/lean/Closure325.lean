import Closure324
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1300 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower1300 : ∀ h, Pure node1300 h → 11 ≤ h.length := by
  apply indexed_extend node1300 [(1, node777), (7, node552), (10, node626), (12, node543), (13, node537)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower777
  · exact lower552
  · exact lower626
  · exact lower543
  · exact lower537
def node1301 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [1, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower1301 : ∀ h, Pure node1301 h → 11 ≤ h.length := by
  apply indexed_extend node1301 [(1, node778), (3, node428), (10, node627), (12, node544)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower778
  · exact lower428
  · exact lower627
  · exact lower544
def node1302 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower1302 : ∀ h, Pure node1302 h → 11 ≤ h.length := by
  apply indexed_extend node1302 [(2, node781), (7, node553), (10, node629), (11, node538)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower781
  · exact lower553
  · exact lower629
  · exact lower538
def node1303 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 2, 1, 0]]
theorem lower1303 : ∀ h, Pure node1303 h → 11 ≤ h.length := by
  apply indexed_extend node1303 [(2, node782), (3, node416), (10, node631), (11, node539)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower782
  · exact lower416
  · exact lower631
  · exact lower539
def entries325 : List Graph := [node1300, node1301, node1302, node1303]
theorem entries_count325 : entries325.length = 4 := by decide +kernel
theorem census_node1300 : ((verts node1300).filter (wye node1300)).length = 5 := by decide +kernel
theorem census_node1301 : ((verts node1301).filter (wye node1301)).length = 4 := by decide +kernel
theorem census_node1302 : ((verts node1302).filter (wye node1302)).length = 4 := by decide +kernel
theorem census_node1303 : ((verts node1303).filter (wye node1303)).length = 4 := by decide +kernel
theorem arc_count325 : (entries325.map (fun g => ((verts g).filter (wye g)).length)).sum = 17 := by
  simp only [entries325, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node1300, census_node1301, census_node1302, census_node1303]
  decide +kernel
end RawCert
