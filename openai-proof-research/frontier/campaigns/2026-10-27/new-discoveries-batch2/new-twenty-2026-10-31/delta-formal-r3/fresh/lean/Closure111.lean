import Closure110
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node444 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower444 : ∀ h, Pure node444 h → 11 ≤ h.length := by
  apply indexed_extend node444 [(5, node85)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower85
def node445 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0], [0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower445 : ∀ h, Pure node445 h → 11 ≤ h.length := by
  apply indexed_extend node445 [(6, node87)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower87
def node446 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 2], [1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower446 : ∀ h, Pure node446 h → 11 ≤ h.length := by
  apply indexed_extend node446 [(5, node86)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower86
def node447 : Graph := [[0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [0, 1, 2, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0], [0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 2, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower447 : ∀ h, Pure node447 h → 11 ≤ h.length := by
  apply indexed_extend node447 [(6, node88)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower88
def entries111 : List Graph := [node444, node445, node446, node447]
theorem entries_count111 : entries111.length = 4 := by decide +kernel
theorem census_node444 : ((verts node444).filter (wye node444)).length = 1 := by decide +kernel
theorem census_node445 : ((verts node445).filter (wye node445)).length = 1 := by decide +kernel
theorem census_node446 : ((verts node446).filter (wye node446)).length = 1 := by decide +kernel
theorem census_node447 : ((verts node447).filter (wye node447)).length = 1 := by decide +kernel
theorem arc_count111 : (entries111.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by
  simp only [entries111, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node444, census_node445, census_node446, census_node447]
  decide +kernel
end RawCert
