import Closure238
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node956 : Graph := [[0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0]]
theorem lower956 : ∀ h, Pure node956 h → 11 ≤ h.length := by
  apply indexed_extend node956 [(7, node274)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower274
def node957 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0], [0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2], [1, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower957 : ∀ h, Pure node957 h → 11 ≤ h.length := by
  apply indexed_extend node957 [(3, node278), (7, node275)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower278
  · exact lower275
def node958 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0], [0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower958 : ∀ h, Pure node958 h → 11 ≤ h.length := by
  apply indexed_extend node958 [(7, node276)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower276
def node959 : Graph := [[0, 3, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0], [3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1], [0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2], [1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 2, 1, 0, 0]]
theorem lower959 : ∀ h, Pure node959 h → 11 ≤ h.length := by
  apply indexed_extend node959 [(3, node279), (6, node275)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower279
  · exact lower275
def entries239 : List Graph := [node956, node957, node958, node959]
theorem entries_count239 : entries239.length = 4 := by decide +kernel
theorem census_node956 : ((verts node956).filter (wye node956)).length = 1 := by decide +kernel
theorem census_node957 : ((verts node957).filter (wye node957)).length = 2 := by decide +kernel
theorem census_node958 : ((verts node958).filter (wye node958)).length = 1 := by decide +kernel
theorem census_node959 : ((verts node959).filter (wye node959)).length = 2 := by decide +kernel
theorem arc_count239 : (entries239.map (fun g => ((verts g).filter (wye g)).length)).sum = 6 := by
  simp only [entries239, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node956, census_node957, census_node958, census_node959]
  decide +kernel
end RawCert
