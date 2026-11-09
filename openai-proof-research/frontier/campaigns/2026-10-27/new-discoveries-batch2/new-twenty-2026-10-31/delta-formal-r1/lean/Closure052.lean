import Closure051
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node208 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 3, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1], [0, 2, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 2], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 1, 2, 1, 0]]
theorem lower208 : ∀ h, Pure node208 h → 11 ≤ h.length := by
  apply indexed_extend node208 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node209 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2], [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0], [0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 1, 1, 0]]
theorem lower209 : ∀ h, Pure node209 h → 11 ≤ h.length := by
  apply indexed_extend node209 [(7, node17)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower17
def node210 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 1], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1], [0, 1, 0, 0, 2, 0, 0, 0, 0, 2, 1, 0], [1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0]]
theorem lower210 : ∀ h, Pure node210 h → 11 ≤ h.length := by
  apply indexed_extend node210 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def node211 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1], [0, 1, 0, 1, 2, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 1], [0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 1, 2, 1, 0]]
theorem lower211 : ∀ h, Pure node211 h → 11 ≤ h.length := by
  apply indexed_extend node211 [] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp at hk
def entries52 : List Graph := [node208, node209, node210, node211]
theorem entries_count52 : entries52.length = 4 := by decide +kernel
theorem arc_count52 : (entries52.map (fun g => ((verts g).filter (wye g)).length)).sum = 1 := by decide +kernel
end RawCert
