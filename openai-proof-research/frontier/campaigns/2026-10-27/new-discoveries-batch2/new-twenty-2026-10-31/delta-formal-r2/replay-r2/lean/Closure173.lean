import Closure172
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node692 : Graph := [[0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0], [0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower692 : ∀ h, Pure node692 h → 11 ≤ h.length := by
  apply indexed_extend node692 [(5, node179)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower179
def node693 : Graph := [[0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]]
theorem lower693 : ∀ h, Pure node693 h → 11 ≤ h.length := by
  apply indexed_extend node693 [(2, node37), (6, node177)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower37
  · exact lower177
def node694 : Graph := [[0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 1, 0, 0, 1, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0], [0, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 2], [3, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0]]
theorem lower694 : ∀ h, Pure node694 h → 11 ≤ h.length := by
  apply indexed_extend node694 [(6, node178)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower178
def node695 : Graph := [[0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0, 0], [2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [1, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 1, 0, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower695 : ∀ h, Pure node695 h → 11 ≤ h.length := by
  apply indexed_extend node695 [(2, node38), (8, node178), (12, node177)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower38
  · exact lower178
  · exact lower177
def entries173 : List Graph := [node692, node693, node694, node695]
theorem entries_count173 : entries173.length = 4 := by decide +kernel
theorem arc_count173 : (entries173.map (fun g => ((verts g).filter (wye g)).length)).sum = 7 := by decide +kernel
end RawCert
