import Closure167
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node672 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [1, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower672 : ∀ h, Pure node672 h → 11 ≤ h.length := by
  apply indexed_extend node672 [(8, node155), (10, node151)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower155
  · exact lower151
def node673 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower673 : ∀ h, Pure node673 h → 11 ≤ h.length := by
  apply indexed_extend node673 [(3, node166), (8, node155), (12, node150)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower166
  · exact lower155
  · exact lower150
def node674 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower674 : ∀ h, Pure node674 h → 11 ≤ h.length := by
  apply indexed_extend node674 [(8, node156), (10, node152)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower156
  · exact lower152
def node675 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0, 0], [0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 1], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower675 : ∀ h, Pure node675 h → 11 ≤ h.length := by
  apply indexed_extend node675 [(3, node167), (8, node156)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower167
  · exact lower156
def entries168 : List Graph := [node672, node673, node674, node675]
theorem entries_count168 : entries168.length = 4 := by decide +kernel
theorem census_node672 : ((verts node672).filter (wye node672)).length = 2 := by decide +kernel
theorem census_node673 : ((verts node673).filter (wye node673)).length = 3 := by decide +kernel
theorem census_node674 : ((verts node674).filter (wye node674)).length = 2 := by decide +kernel
theorem census_node675 : ((verts node675).filter (wye node675)).length = 2 := by decide +kernel
theorem arc_count168 : (entries168.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries168, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node672, census_node673, census_node674, census_node675]
  decide +kernel
end RawCert
