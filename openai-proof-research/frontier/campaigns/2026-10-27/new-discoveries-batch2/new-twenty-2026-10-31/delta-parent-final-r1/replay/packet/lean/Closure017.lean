import Closure016
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node68 : Graph := [[0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 3, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 3], [1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1], [0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0], [1, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 1, 0, 0, 1, 0, 0]]
theorem lower68 : ∀ h, Pure node68 h → 11 ≤ h.length := by
  apply indexed_extend node68 [(7, node3)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower3
def node69 : Graph := [[0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 1, 1, 0, 0, 0, 0, 1], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0]]
theorem lower69 : ∀ h, Pure node69 h → 11 ≤ h.length := by
  apply indexed_extend node69 [(8, node3)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower3
def node70 : Graph := [[0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0], [0, 0, 3, 0, 0, 0, 2, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [1, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 2], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0], [1, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 0], [0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 1, 2, 0, 0]]
theorem lower70 : ∀ h, Pure node70 h → 11 ≤ h.length := by
  apply indexed_extend node70 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node71 : Graph := [[0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0], [0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 1], [1, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 2], [3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 1, 0, 1, 2, 0, 0]]
theorem lower71 : ∀ h, Pure node71 h → 11 ≤ h.length := by
  apply indexed_extend node71 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries17 : List Graph := [node68, node69, node70, node71]
theorem entries_count17 : entries17.length = 4 := by decide +kernel
theorem arc_count17 : (entries17.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
