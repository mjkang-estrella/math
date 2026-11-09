import Closure225
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node904 : Graph := [[0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2], [0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 3, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 1, 1, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0], [2, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2], [0, 0, 3, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0, 3, 1, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]
theorem lower904 : ∀ h, Pure node904 h → 11 ≤ h.length := by
  apply indexed_extend node904 [(0, node37), (6, node254), (12, node272)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower37
  · exact lower254
  · exact lower272
def node905 : Graph := [[0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 0, 1, 1, 0, 1, 0, 0, 3, 0, 0, 0], [0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2], [2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 1, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0]]
theorem lower905 : ∀ h, Pure node905 h → 11 ≤ h.length := by
  apply indexed_extend node905 [(0, node38), (11, node273), (12, node254)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower38
  · exact lower273
  · exact lower254
def node906 : Graph := [[0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0], [0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0], [0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2], [0, 0, 3, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 2], [2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0]]
theorem lower906 : ∀ h, Pure node906 h → 11 ≤ h.length := by
  apply indexed_extend node906 [(0, node39), (11, node274)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower39
  · exact lower274
def node907 : Graph := [[0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], [0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0], [0, 0, 1, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 3, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 2, 0, 0, 1, 0, 1, 0]]
theorem lower907 : ∀ h, Pure node907 h → 11 ≤ h.length := by
  apply indexed_extend node907 [(1, node75), (7, node255)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower75
  · exact lower255
def entries226 : List Graph := [node904, node905, node906, node907]
theorem entries_count226 : entries226.length = 4 := by decide +kernel
theorem arc_count226 : (entries226.map (fun g => ((verts g).filter (wye g)).length)).sum = 10 := by decide +kernel
end RawCert
