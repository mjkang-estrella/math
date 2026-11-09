import Closure246
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node988 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 0], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower988 : ∀ h, Pure node988 h → 11 ≤ h.length := by
  apply indexed_extend node988 [(1, node341), (2, node329), (4, node347), (13, node301)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower341
  · exact lower329
  · exact lower347
  · exact lower301
def node989 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower989 : ∀ h, Pure node989 h → 11 ≤ h.length := by
  apply indexed_extend node989 [(1, node342), (2, node330), (5, node404), (8, node310)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower342
  · exact lower330
  · exact lower404
  · exact lower310
def node990 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower990 : ∀ h, Pure node990 h → 11 ≤ h.length := by
  apply indexed_extend node990 [(1, node343), (2, node331), (7, node308), (8, node311)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower343
  · exact lower331
  · exact lower308
  · exact lower311
def node991 : Graph := [[0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]]
theorem lower991 : ∀ h, Pure node991 h → 11 ≤ h.length := by
  apply indexed_extend node991 [(1, node344), (2, node332), (5, node405), (7, node309), (9, node308)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact lower344
  · exact lower332
  · exact lower405
  · exact lower309
  · exact lower308
def entries247 : List Graph := [node988, node989, node990, node991]
theorem entries_count247 : entries247.length = 4 := by decide +kernel
theorem census_node988 : ((verts node988).filter (wye node988)).length = 4 := by decide +kernel
theorem census_node989 : ((verts node989).filter (wye node989)).length = 4 := by decide +kernel
theorem census_node990 : ((verts node990).filter (wye node990)).length = 4 := by decide +kernel
theorem census_node991 : ((verts node991).filter (wye node991)).length = 5 := by decide +kernel
theorem arc_count247 : (entries247.map (fun g => ((verts g).filter (wye g)).length)).sum = 17 := by
  simp only [entries247, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node988, census_node989, census_node990, census_node991]
  decide +kernel
end RawCert
