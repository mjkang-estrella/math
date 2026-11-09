import Closure059
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node240 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3], [3, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1], [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 1, 0, 0, 0, 2, 1, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0]]
theorem lower240 : ∀ h, Pure node240 h → 11 ≤ h.length := by
  apply indexed_extend node240 [(8, node19)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower19
def node241 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 3, 0], [3, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0], [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 1, 2, 0, 0]]
theorem lower241 : ∀ h, Pure node241 h → 11 ≤ h.length := by
  apply indexed_extend node241 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node242 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 3, 0], [3, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0], [1, 0, 1, 0, 1, 0, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 1, 0, 1, 0, 1, 2, 0, 0]]
theorem lower242 : ∀ h, Pure node242 h → 11 ≤ h.length := by
  apply indexed_extend node242 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node243 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 2, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0], [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [1, 0, 1, 1, 1, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0]]
theorem lower243 : ∀ h, Pure node243 h → 11 ≤ h.length := by
  apply indexed_extend node243 [(11, node19)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower19
def entries60 : List Graph := [node240, node241, node242, node243]
theorem entries_count60 : entries60.length = 4 := by decide +kernel
theorem arc_count60 : (entries60.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
