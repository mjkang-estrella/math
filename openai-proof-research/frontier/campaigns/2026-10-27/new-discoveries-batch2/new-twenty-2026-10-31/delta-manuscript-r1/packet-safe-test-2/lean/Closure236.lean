import Closure235
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node944 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1], [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 0]]
theorem lower944 : ∀ h, Pure node944 h → 11 ≤ h.length := by
  apply indexed_extend node944 [(8, node266)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower266
def node945 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1], [0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1], [2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 3], [1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1], [0, 0, 3, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 0]]
theorem lower945 : ∀ h, Pure node945 h → 11 ≤ h.length := by
  apply indexed_extend node945 [(4, node272), (7, node267), (8, node268)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower272
  · exact lower267
  · exact lower268
def node946 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3], [1, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0]]
theorem lower946 : ∀ h, Pure node946 h → 11 ≤ h.length := by
  apply indexed_extend node946 [(3, node272), (6, node278), (7, node269)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower272
  · exact lower278
  · exact lower269
def node947 : Graph := [[0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0]]
theorem lower947 : ∀ h, Pure node947 h → 11 ≤ h.length := by
  apply indexed_extend node947 [(7, node270), (12, node263)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower270
  · exact lower263
def entries236 : List Graph := [node944, node945, node946, node947]
theorem entries_count236 : entries236.length = 4 := by decide +kernel
theorem census_node944 : ((verts node944).filter (wye node944)).length = 1 := by decide +kernel
theorem census_node945 : ((verts node945).filter (wye node945)).length = 3 := by decide +kernel
theorem census_node946 : ((verts node946).filter (wye node946)).length = 3 := by decide +kernel
theorem census_node947 : ((verts node947).filter (wye node947)).length = 2 := by decide +kernel
theorem arc_count236 : (entries236.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by
  simp only [entries236, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node944, census_node945, census_node946, census_node947]
  decide +kernel
end RawCert
