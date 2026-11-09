import Closure079
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node320 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [2, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower320 : ∀ h, Pure node320 h → 11 ≤ h.length := by
  apply indexed_extend node320 [(3, node92), (9, node41)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower92
  · exact lower41
def node321 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower321 : ∀ h, Pure node321 h → 11 ≤ h.length := by
  apply indexed_extend node321 [(4, node70)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower70
def node322 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 1], [2, 0, 0, 2, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 2, 0], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower322 : ∀ h, Pure node322 h → 11 ≤ h.length := by
  apply indexed_extend node322 [(6, node42)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower42
def node323 : Graph := [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 3], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0]]
theorem lower323 : ∀ h, Pure node323 h → 11 ≤ h.length := by
  apply indexed_extend node323 [(4, node68), (8, node40), (9, node41)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower68
  · exact lower40
  · exact lower41
def entries80 : List Graph := [node320, node321, node322, node323]
theorem entries_count80 : entries80.length = 4 := by decide +kernel
theorem arc_count80 : (entries80.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by decide +kernel
end RawCert
