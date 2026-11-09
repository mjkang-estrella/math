import Closure015
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node64 : Graph := [[0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0], [0, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 1], [1, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 1, 0, 1, 2, 0, 0]]
theorem lower64 : ∀ h, Pure node64 h → 11 ≤ h.length := by
  apply indexed_extend node64 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node65 : Graph := [[0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0], [0, 0, 3, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0], [1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 2], [1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0]]
theorem lower65 : ∀ h, Pure node65 h → 11 ≤ h.length := by
  apply indexed_extend node65 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node66 : Graph := [[0, 0, 0, 1, 0, 1, 0, 1, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 1, 1], [1, 0, 0, 0, 0, 0, 1, 2, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 1], [1, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0]]
theorem lower66 : ∀ h, Pure node66 h → 11 ≤ h.length := by
  apply indexed_extend node66 [(2, node9)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower9
def node67 : Graph := [[0, 0, 0, 1, 0, 1, 0, 1, 0, 3, 0, 0], [0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 1, 0, 1, 1], [1, 0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 2], [1, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [3, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0]]
theorem lower67 : ∀ h, Pure node67 h → 11 ≤ h.length := by
  apply indexed_extend node67 [(2, node10)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower10
def entries16 : List Graph := [node64, node65, node66, node67]
theorem entries_count16 : entries16.length = 4 := by decide +kernel
theorem arc_count16 : (entries16.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
