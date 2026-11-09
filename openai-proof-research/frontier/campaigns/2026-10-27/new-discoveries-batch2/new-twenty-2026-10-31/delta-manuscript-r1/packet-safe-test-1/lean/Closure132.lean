import Closure131
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node528 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 1], [1, 0, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 2, 0, 0]]
theorem lower528 : ∀ h, Pure node528 h → 11 ≤ h.length := by
  apply indexed_extend node528 [(3, node71), (11, node134)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower71
  · exact lower134
def node529 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0], [1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower529 : ∀ h, Pure node529 h → 11 ≤ h.length := by
  apply indexed_extend node529 [(7, node111), (11, node137)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower111
  · exact lower137
def node530 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0], [1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower530 : ∀ h, Pure node530 h → 11 ≤ h.length := by
  apply indexed_extend node530 [(7, node112), (11, node138)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower112
  · exact lower138
def node531 : Graph := [[0, 0, 0, 2, 1, 0, 0, 0, 1, 0, 0, 2, 0], [0, 0, 3, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2], [0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1], [1, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0]]
theorem lower531 : ∀ h, Pure node531 h → 11 ≤ h.length := by
  apply indexed_extend node531 [(3, node63), (6, node111)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower63
  · exact lower111
def entries132 : List Graph := [node528, node529, node530, node531]
theorem entries_count132 : entries132.length = 4 := by decide +kernel
theorem census_node528 : ((verts node528).filter (wye node528)).length = 2 := by decide +kernel
theorem census_node529 : ((verts node529).filter (wye node529)).length = 2 := by decide +kernel
theorem census_node530 : ((verts node530).filter (wye node530)).length = 2 := by decide +kernel
theorem census_node531 : ((verts node531).filter (wye node531)).length = 2 := by decide +kernel
theorem arc_count132 : (entries132.map (fun g => ((verts g).filter (wye g)).length)).sum = 8 := by
  simp only [entries132, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node528, census_node529, census_node530, census_node531]
  decide +kernel
end RawCert
