import Closure104
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node420 : Graph := [[0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower420 : ∀ h, Pure node420 h → 11 ≤ h.length := by
  apply indexed_extend node420 [(1, node162), (7, node72), (12, node68)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower162
  · exact lower72
  · exact lower68
def node421 : Graph := [[0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 3, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower421 : ∀ h, Pure node421 h → 11 ≤ h.length := by
  apply indexed_extend node421 [(5, node74), (7, node73), (12, node68)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower74
  · exact lower73
  · exact lower68
def node422 : Graph := [[0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [1, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower422 : ∀ h, Pure node422 h → 11 ≤ h.length := by
  apply indexed_extend node422 [(1, node163), (8, node72), (12, node69)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower163
  · exact lower72
  · exact lower69
def node423 : Graph := [[0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [1, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower423 : ∀ h, Pure node423 h → 11 ≤ h.length := by
  apply indexed_extend node423 [(1, node164), (11, node70)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower164
  · exact lower70
def entries105 : List Graph := [node420, node421, node422, node423]
theorem entries_count105 : entries105.length = 4 := by decide +kernel
theorem census_node420 : ((verts node420).filter (wye node420)).length = 3 := by decide +kernel
theorem census_node421 : ((verts node421).filter (wye node421)).length = 3 := by decide +kernel
theorem census_node422 : ((verts node422).filter (wye node422)).length = 3 := by decide +kernel
theorem census_node423 : ((verts node423).filter (wye node423)).length = 2 := by decide +kernel
theorem arc_count105 : (entries105.map (fun g => ((verts g).filter (wye g)).length)).sum = 11 := by
  simp only [entries105, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node420, census_node421, census_node422, census_node423]
  decide +kernel
end RawCert
