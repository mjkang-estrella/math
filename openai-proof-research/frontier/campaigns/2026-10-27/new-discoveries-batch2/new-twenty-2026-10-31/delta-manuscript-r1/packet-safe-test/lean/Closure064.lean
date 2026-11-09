import Closure063
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node256 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 1, 2, 0, 0, 1, 1, 0, 1, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 1], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0]]
theorem lower256 : ∀ h, Pure node256 h → 11 ≤ h.length := by
  apply indexed_extend node256 [(1, node5)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower5
def node257 : Graph := [[0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 1, 0, 0, 3, 0, 0], [1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 1, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 3, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower257 : ∀ h, Pure node257 h → 11 ≤ h.length := by
  apply indexed_extend node257 [(1, node12), (11, node24)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower12
  · exact lower24
def node258 : Graph := [[0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 1, 1, 0, 3, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 1, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 0, 1, 0, 2, 2, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower258 : ∀ h, Pure node258 h → 11 ≤ h.length := by
  apply indexed_extend node258 [(1, node13)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower13
def node259 : Graph := [[0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 1], [1, 0, 0, 1, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 2], [2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 1, 0]]
theorem lower259 : ∀ h, Pure node259 h → 11 ≤ h.length := by
  apply indexed_extend node259 [(1, node14)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower14
def entries64 : List Graph := [node256, node257, node258, node259]
theorem entries_count64 : entries64.length = 4 := by decide +kernel
theorem census_node256 : ((verts node256).filter (wye node256)).length = 1 := by decide +kernel
theorem census_node257 : ((verts node257).filter (wye node257)).length = 2 := by decide +kernel
theorem census_node258 : ((verts node258).filter (wye node258)).length = 1 := by decide +kernel
theorem census_node259 : ((verts node259).filter (wye node259)).length = 1 := by decide +kernel
theorem arc_count64 : (entries64.map (fun g => ((verts g).filter (wye g)).length)).sum = 5 := by
  simp only [entries64, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, census_node256, census_node257, census_node258, census_node259]
  decide +kernel
end RawCert
