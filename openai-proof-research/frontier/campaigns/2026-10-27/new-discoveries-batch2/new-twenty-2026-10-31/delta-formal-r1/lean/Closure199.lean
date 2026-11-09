import Closure198
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node796 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 1, 0], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1], [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 2], [0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0]]
theorem lower796 : ∀ h, Pure node796 h → 11 ≤ h.length := by
  apply indexed_extend node796 [(4, node216)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower216
def node797 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 1], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 3, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0, 2, 0, 0, 1, 1, 0]]
theorem lower797 : ∀ h, Pure node797 h → 11 ≤ h.length := by
  apply indexed_extend node797 [(7, node210)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower210
def node798 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0], [3, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1], [2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2], [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2], [0, 3, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 1, 0]]
theorem lower798 : ∀ h, Pure node798 h → 11 ≤ h.length := by
  apply indexed_extend node798 [(7, node211)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower211
def node799 : Graph := [[0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1], [2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0], [0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 1, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 0, 0, 2, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0], [0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0]]
theorem lower799 : ∀ h, Pure node799 h → 11 ≤ h.length := by
  apply indexed_extend node799 [(5, node229)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_singleton] at hk
  rcases hk with rfl
  · exact lower229
def entries199 : List Graph := [node796, node797, node798, node799]
theorem entries_count199 : entries199.length = 4 := by decide +kernel
theorem arc_count199 : (entries199.map (fun g => ((verts g).filter (wye g)).length)).sum = 4 := by decide +kernel
end RawCert
