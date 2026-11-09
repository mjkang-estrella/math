import Closure039
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node160 : Graph := [[0, 0, 1, 0, 1, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [1, 0, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 1], [1, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 1, 0, 0, 0, 2, 1, 0]]
theorem lower160 : ∀ h, Pure node160 h → 11 ≤ h.length := by
  apply indexed_extend node160 [(9, node9)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower9
def node161 : Graph := [[0, 0, 1, 0, 1, 0, 1, 0, 3, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1], [1, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 2], [1, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 1, 0]]
theorem lower161 : ∀ h, Pure node161 h → 11 ≤ h.length := by
  apply indexed_extend node161 [(9, node10)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower10
def node162 : Graph := [[0, 0, 1, 1, 0, 0, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3, 0], [1, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0], [0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [1, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower162 : ∀ h, Pure node162 h → 11 ≤ h.length := by
  apply indexed_extend node162 [(6, node11)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower11
def node163 : Graph := [[0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0], [1, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 0], [0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1], [1, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0]]
theorem lower163 : ∀ h, Pure node163 h → 11 ≤ h.length := by
  apply indexed_extend node163 [(7, node11)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower11
def entries40 : List Graph := [node160, node161, node162, node163]
theorem entries_count40 : entries40.length = 4 := by decide +kernel
theorem arc_count40 : (entries40.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by decide +kernel
end RawCert
