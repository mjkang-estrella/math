import Closure061
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node248 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 2, 1, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 1, 0, 0, 2, 1, 0]]
theorem lower248 : ∀ h, Pure node248 h → 11 ≤ h.length := by
  apply indexed_extend node248 [(9, node21)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower21
def node249 : Graph := [[0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 0], [3, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0], [0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0, 2, 0, 0, 0, 1], [1, 0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2], [0, 3, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 1, 0, 1, 1, 0, 1, 2, 0, 0]]
theorem lower249 : ∀ h, Pure node249 h → 11 ≤ h.length := by
  apply indexed_extend node249 [(9, node21)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower21
def node250 : Graph := [[0, 0, 3, 2, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3], [3, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0], [0, 0, 2, 1, 0, 2, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1], [1, 0, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 2], [0, 0, 0, 1, 0, 1, 0, 0, 3, 1, 0, 0], [0, 3, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0]]
theorem lower250 : ∀ h, Pure node250 h → 11 ≤ h.length := by
  apply indexed_extend node250 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node251 : Graph := [[0, 0, 3, 2, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3], [3, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1], [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0], [0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0]]
theorem lower251 : ∀ h, Pure node251 h → 11 ≤ h.length := by
  apply indexed_extend node251 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries62 : List Graph := [node248, node249, node250, node251]
theorem entries_count62 : entries62.length = 4 := by decide +kernel
theorem arc_count62 : (entries62.map (fun g => ((verts g).filter (wye g)).length)).sum = 2 := by decide +kernel
end RawCert
