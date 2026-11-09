import Closure248
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node996 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0]]
theorem lower996 : ∀ h, Pure node996 h → 11 ≤ h.length := by
  apply indexed_extend node996 [(2, node337), (5, node412), (8, node312), (10, node309), (12, node305)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower337
  · exact lower412
  · exact lower312
  · exact lower309
  · exact lower305
def node997 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 0, 2], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 2, 0, 0, 0]]
theorem lower997 : ∀ h, Pure node997 h → 11 ≤ h.length := by
  apply indexed_extend node997 [(2, node338), (5, node413), (10, node310), (12, node306)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower338
  · exact lower413
  · exact lower310
  · exact lower306
def node998 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 2, 0, 0, 0]]
theorem lower998 : ∀ h, Pure node998 h → 11 ≤ h.length := by
  apply indexed_extend node998 [(2, node339), (7, node312), (10, node311), (12, node307)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower339
  · exact lower312
  · exact lower311
  · exact lower307
def node999 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0]]
theorem lower999 : ∀ h, Pure node999 h → 11 ≤ h.length := by
  apply indexed_extend node999 [(4, node351), (5, node407), (13, node300)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower351
  · exact lower407
  · exact lower300
def entries249 : List Graph := [node996, node997, node998, node999]
theorem entries_count249 : entries249.length = 4 := by decide +kernel
theorem census_node996 : ((verts node996).filter (wye node996)).length = 5 := by decide +kernel
theorem census_node997 : ((verts node997).filter (wye node997)).length = 4 := by decide +kernel
theorem census_node998 : ((verts node998).filter (wye node998)).length = 4 := by decide +kernel
theorem census_node999 : ((verts node999).filter (wye node999)).length = 3 := by decide +kernel
theorem arc_count249 : (entries249.map (fun g => ((verts g).filter (wye g)).length)).sum = 16 := by
  simp only [entries249, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node996, census_node997, census_node998, census_node999]
  decide +kernel
end RawCert
