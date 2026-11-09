import Closure085
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node344 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1], [0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]]
theorem lower344 : ∀ h, Pure node344 h → 11 ≤ h.length := by
  apply indexed_extend node344 [(4, node152), (8, node50)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower152
  · exact lower50
def node345 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 1], [0, 1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1], [0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2], [3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 1, 1, 2, 0, 0, 0]]
theorem lower345 : ∀ h, Pure node345 h → 11 ≤ h.length := by
  apply indexed_extend node345 [(3, node95), (9, node50)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower95
  · exact lower50
def node346 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 1, 0], [0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower346 : ∀ h, Pure node346 h → 11 ≤ h.length := by
  apply indexed_extend node346 [(1, node93), (4, node72), (12, node40)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower93
  · exact lower72
  · exact lower40
def node347 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0], [2, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 0], [0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower347 : ∀ h, Pure node347 h → 11 ≤ h.length := by
  apply indexed_extend node347 [(1, node94), (12, node41)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower94
  · exact lower41
def entries86 : List Graph := [node344, node345, node346, node347]
theorem entries_count86 : entries86.length = 4 := by decide +kernel
theorem arc_count86 : (entries86.map (fun g => ((verts g).filter (wye g)).length)).sum = 9 := by decide +kernel
end RawCert
