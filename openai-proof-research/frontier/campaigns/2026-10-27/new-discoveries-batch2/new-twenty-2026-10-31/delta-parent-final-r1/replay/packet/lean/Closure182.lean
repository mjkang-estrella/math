import Closure181
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node728 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0]]
theorem lower728 : ∀ h, Pure node728 h → 11 ≤ h.length := by
  apply indexed_extend node728 [(0, node33), (4, node204), (12, node182)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower33
  · exact lower204
  · exact lower182
def node729 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 3, 0, 0], [2, 0, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 2], [0, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 2, 0, 0]]
theorem lower729 : ∀ h, Pure node729 h → 11 ≤ h.length := by
  apply indexed_extend node729 [(0, node34), (2, node102), (9, node219)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower34
  · exact lower102
  · exact lower219
def node730 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 2], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 1, 0, 2, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 1, 0]]
theorem lower730 : ∀ h, Pure node730 h → 11 ≤ h.length := by
  apply indexed_extend node730 [(0, node144), (6, node184)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact lower144
  · exact lower184
def node731 : Graph := [[0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0], [2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0], [0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 1], [2, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], [0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0], [2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2], [0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 1, 0]]
theorem lower731 : ∀ h, Pure node731 h → 11 ≤ h.length := by
  apply indexed_extend node731 [(0, node145), (2, node103), (6, node185), (9, node220)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower145
  · exact lower103
  · exact lower185
  · exact lower220
def entries182 : List Graph := [node728, node729, node730, node731]
theorem entries_count182 : entries182.length = 4 := by decide +kernel
theorem arc_count182 : (entries182.map (fun g => ((verts g).filter (wye g)).length)).sum = 12 := by decide +kernel
end RawCert
