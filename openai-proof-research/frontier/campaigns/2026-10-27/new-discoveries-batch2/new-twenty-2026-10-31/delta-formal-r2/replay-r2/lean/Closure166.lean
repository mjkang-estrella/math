import Closure165
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node664 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1], [1, 0, 1, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower664 : ∀ h, Pure node664 h → 11 ≤ h.length := by
  apply indexed_extend node664 [(3, node163), (8, node150)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower163
  · exact lower150
def node665 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 2], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [1, 0, 1, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0, 0]]
theorem lower665 : ∀ h, Pure node665 h → 11 ≤ h.length := by
  apply indexed_extend node665 [(3, node164), (9, node151)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower164
  · exact lower151
def node666 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1], [1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 0, 0]]
theorem lower666 : ∀ h, Pure node666 h → 11 ≤ h.length := by
  apply indexed_extend node666 [(3, node165), (9, node152)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower165
  · exact lower152
def node667 : Graph := [[0, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [1, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 2], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower667 : ∀ h, Pure node667 h → 11 ≤ h.length := by
  apply indexed_extend node667 [(6, node161), (8, node153), (10, node147)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower161
  · exact lower153
  · exact lower147
def entries166 : List Graph := [node664, node665, node666, node667]
theorem entries_count166 : entries166.length = 4 := by decide +kernel
theorem arc_count166 : (entries166.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by decide +kernel
end RawCert
