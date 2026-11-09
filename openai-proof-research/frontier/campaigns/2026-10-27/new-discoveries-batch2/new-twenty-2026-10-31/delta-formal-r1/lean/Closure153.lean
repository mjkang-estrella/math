import Closure152
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node612 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2, 0], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1], [0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0], [1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0], [0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1], [0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 1, 0]]
theorem lower612 : ∀ h, Pure node612 h → 11 ≤ h.length := by
  apply indexed_extend node612 [(2, node234), (6, node130), (7, node131)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower234
  · exact lower130
  · exact lower131
def node613 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 1], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower613 : ∀ h, Pure node613 h → 11 ≤ h.length := by
  apply indexed_extend node613 [(5, node132), (10, node127)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower132
  · exact lower127
def node614 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0], [3, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 1], [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2], [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 1], [0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 2, 0]]
theorem lower614 : ∀ h, Pure node614 h → 11 ≤ h.length := by
  apply indexed_extend node614 [(5, node133), (6, node134)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower133
  · exact lower134
def node615 : Graph := [[0, 0, 0, 3, 1, 0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2], [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0], [0, 0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 1, 0]]
theorem lower615 : ∀ h, Pure node615 h → 11 ≤ h.length := by
  apply indexed_extend node615 [(5, node132), (7, node137), (10, node128)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower132
  · exact lower137
  · exact lower128
def entries153 : List Graph := [node612, node613, node614, node615]
theorem entries_count153 : entries153.length = 4 := by decide +kernel
theorem arc_count153 : (entries153.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by decide +kernel
end RawCert
