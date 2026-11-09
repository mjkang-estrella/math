import Closure156
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node628 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower628 : ∀ h, Pure node628 h → 11 ≤ h.length := by
  apply indexed_extend node628 [(2, node245), (12, node137)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower245
  · exact lower137
def node629 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1, 0]]
theorem lower629 : ∀ h, Pure node629 h → 11 ≤ h.length := by
  apply indexed_extend node629 [(2, node246), (10, node130)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower246
  · exact lower130
def node630 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower630 : ∀ h, Pure node630 h → 11 ≤ h.length := by
  apply indexed_extend node630 [(2, node247), (10, node130), (11, node138)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower247
  · exact lower130
  · exact lower138
def node631 : Graph := [[0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 1], [1, 0, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 2, 1, 0]]
theorem lower631 : ∀ h, Pure node631 h → 11 ≤ h.length := by
  apply indexed_extend node631 [(2, node248), (10, node131)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower248
  · exact lower131
def entries157 : List Graph := [node628, node629, node630, node631]
theorem entries_count157 : entries157.length = 4 := by decide +kernel
theorem census_node628 : ((verts node628).filter (wye node628)).length = 2 := by decide +kernel
theorem census_node629 : ((verts node629).filter (wye node629)).length = 2 := by decide +kernel
theorem census_node630 : ((verts node630).filter (wye node630)).length = 3 := by decide +kernel
theorem census_node631 : ((verts node631).filter (wye node631)).length = 2 := by decide +kernel
theorem arc_count157 : (entries157.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries157, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node628, census_node629, census_node630, census_node631]
  decide +kernel
end RawCert
