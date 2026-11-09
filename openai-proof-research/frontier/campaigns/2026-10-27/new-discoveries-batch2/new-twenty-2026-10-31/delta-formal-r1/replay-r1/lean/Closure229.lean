import Closure228
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node916 : Graph := [[0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0, 3, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower916 : ∀ h, Pure node916 h → 11 ≤ h.length := by
  apply indexed_extend node916 [(1, node168), (6, node257), (12, node278)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower168
  · exact lower257
  · exact lower278
def node917 : Graph := [[0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower917 : ∀ h, Pure node917 h → 11 ≤ h.length := by
  apply indexed_extend node917 [(1, node169), (5, node257), (12, node279)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower169
  · exact lower257
  · exact lower279
def node918 : Graph := [[0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0], [0, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 2], [0, 0, 3, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 3, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower918 : ∀ h, Pure node918 h → 11 ≤ h.length := by
  apply indexed_extend node918 [(1, node170), (12, node280)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower170
  · exact lower280
def node919 : Graph := [[0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0], [0, 0, 1, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0], [0, 0, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower919 : ∀ h, Pure node919 h → 11 ≤ h.length := by
  apply indexed_extend node919 [(1, node171), (6, node258)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower171
  · exact lower258
def entries229 : List Graph := [node916, node917, node918, node919]
theorem entries_count229 : entries229.length = 4 := by decide +kernel
theorem arc_count229 : (entries229.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by decide +kernel
end RawCert
