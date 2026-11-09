import Closure052
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node212 : Graph := [[0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 3, 0], [3, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 2], [1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 1, 0]]
theorem lower212 : ∀ h, Pure node212 h → 11 ≤ h.length := by
  apply indexed_extend node212 [(5, node20)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower20
def node213 : Graph := [[0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 3, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 1], [1, 0, 1, 0, 0, 0, 1, 0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0]]
theorem lower213 : ∀ h, Pure node213 h → 11 ≤ h.length := by
  apply indexed_extend node213 [(5, node21), (8, node17)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower21
  · exact lower17
def node214 : Graph := [[0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 1, 0, 2, 1, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 1, 0, 2, 1, 0]]
theorem lower214 : ∀ h, Pure node214 h → 11 ≤ h.length := by
  apply indexed_extend node214 [(3, node18), (9, node17)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower18
  · exact lower17
def node215 : Graph := [[0, 0, 3, 0, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0], [2, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 0, 1, 1, 1, 2, 0, 0]]
theorem lower215 : ∀ h, Pure node215 h → 11 ≤ h.length := by
  apply indexed_extend node215 [(9, node17)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower17
def entries53 : List Graph := [node212, node213, node214, node215]
theorem entries_count53 : entries53.length = 4 := by decide +kernel
theorem arc_count53 : (entries53.map (fun g => ((verts g).filter (wye g)).length)).sum = 6 := by decide +kernel
end RawCert
