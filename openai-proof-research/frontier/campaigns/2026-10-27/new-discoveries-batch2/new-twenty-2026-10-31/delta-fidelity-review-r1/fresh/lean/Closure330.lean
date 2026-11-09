import Closure329
namespace RawCert
open Delta153 RawClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
def node1320 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2], [0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 2, 1, 0]]
theorem lower1320 : ∀ h, Pure node1320 h → 11 ≤ h.length := by
  apply indexed_extend node1320 [(4, node581), (5, node578), (9, node567), (11, node560)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower581
  · exact lower578
  · exact lower567
  · exact lower560
def node1321 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 1], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2], [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 2, 0]]
theorem lower1321 : ∀ h, Pure node1321 h → 11 ≤ h.length := by
  apply indexed_extend node1321 [(5, node579), (8, node565), (9, node568)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower579
  · exact lower565
  · exact lower568
def node1322 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 3], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0], [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 1, 1], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0], [0, 1, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 0, 0, 1, 1, 0, 0, 1, 0]]
theorem lower1322 : ∀ h, Pure node1322 h → 11 ≤ h.length := by
  apply indexed_extend node1322 [(5, node580), (6, node605), (7, node564), (11, node560)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact lower580
  · exact lower605
  · exact lower564
  · exact lower560
def node1323 : Graph := [[0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0], [0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0], [3, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 3, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0], [2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 2, 0, 0, 1, 0, 2, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2], [0, 2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0]]
theorem lower1323 : ∀ h, Pure node1323 h → 11 ≤ h.length := by
  apply indexed_extend node1323 [(5, node582), (8, node566), (13, node560)] (by decide +kernel) (by decide +kernel)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact lower582
  · exact lower566
  · exact lower560
def entries330 : List Graph := [node1320, node1321, node1322, node1323]
theorem entries_count330 : entries330.length = 4 := by decide +kernel
theorem arc_count330 : (entries330.map (fun g => ((verts g).filter (wye g)).length)).sum = 14 := by decide +kernel
end RawCert
